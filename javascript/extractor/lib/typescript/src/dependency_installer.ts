/**
 * Usage: dependency_installer FILES...
 *
 * Given a set of package.json files, attempts to behave as 'npm install' except only
 * doing as much work as is necessary to install the relevant `.d.ts` files.
 *
 * This means only installing packages containing such files, and not running scripts
 * or checking engine/platform requirements etc.
 */

import * as fs from "fs";
import * as npa from "npm-package-arg";
import * as pacote from "pacote";
import * as pathlib from "path";
import { rateLimit } from "./rate_limiter";

/**
 * Parses an entry from the `{peer,dev,}dependencies` part of a package.json file.
 *
 * Return `null` if the entry does not refer to a package from a registry, such as
 * a `file:` dependency.
 */
function getRegistrySpec(name: string, spec: string): npa.RegistryResult | null {
    let result: npa.Result;
    try {
        result = npa.resolve(name, spec);
    } catch (e) {
        return null;
    }
    if (result.type === "alias") {
        result = (result as npa.AliasResult).subSpec;
    }
    switch (result.type) {
        case "version":
        case "range":
        case "tag":
            return result as npa.RegistryResult;
    }
    return null;
}

/**
 * Some additional package.json properties we expect to find in a full manifest.
 */
interface FullManifest extends pacote.ManifestResult {
    /** Path to the `.d.ts` file. */
    types?: string;

    /** Synonym for `types`. */
    typings?: string;
}

/**
 * Fetches the manifest for a package, including `types` and `typings` fields.
 */
function getFullManifest_(spec: npa.RegistryResult): Promise<FullManifest> {
    return pacote.manifest(spec.raw, { fullMetadata: true });
}
let getFullManifest = rateLimit(getFullManifest_);

const packageNameRex = /^(?:@[\w.-]+\/)?\w[\w.-]*$/;
/**
 * Returns true if `name` is a valid package name.
 *
 * This is also checked by `npm-package-arg` and `pacote`, but to alleviate
 * path traversal paranoia we check it again.
 */
function isPackageName(name: string) {
    return packageNameRex.test(name);
}

let alreadyInstalled = new Set<string>();

/**
 * Install the given package relative to a package.json file in `baseDir`.
 */
async function installPackage_(baseDir: string, spec: npa.RegistryResult): Promise<boolean> {
    let { name } = spec;
    if (name == null || !isPackageName(name)) {
        return false;
    }
    let hash = baseDir + '::' + name;
    if (alreadyInstalled.has(hash)) {
        return false;
    }
    alreadyInstalled.add(hash);
    let destDir = pathlib.join(baseDir, 'node_modules', name);
    if (fs.existsSync(destDir)) {
        return false;
    }
    console.warn(`Installing ${spec.raw} to ${destDir}`);
    await pacote.extract(spec.raw, destDir);
    return true;
}
let installPackage = rateLimit(installPackage_);

/**
 * Install the given package and all its dependencies.
 *
 * We only do this for packages in `@types` and `devDependencies` are not followed.
 */
async function installPackageWithTypeDependencies(baseDir: string, spec: npa.RegistryResult): Promise<unknown> {
    let wasInstalled = await installPackage(baseDir, spec);
    if (!wasInstalled) {
        return;
    }
    let manifest = await getFullManifest(spec);
    let dependencyFields = ['dependencies', 'peerDependencies'];
    let promises = [];
    for (let field of dependencyFields) {
        let dependencies = (manifest[field] || {}) as Record<string, string>;
        for (let name of Object.getOwnPropertyNames(dependencies)) {
            let target = dependencies[name];
            if (typeof target !== 'string') continue;
            let targetSpec = getRegistrySpec(name, target);
            if (targetSpec == null) continue;
            promises.push(installIfPackageHasTypings(baseDir, targetSpec));
        }
    }
    return Promise.all(promises);
}

/**
 * Checks if the given package contains typings and installs it if it does, along with
 * any transitive dependencies that are deemed necessary.
 */
async function installIfPackageHasTypings(baseDir: string, spec: npa.RegistryResult) {
    if (spec.scope === '@types') {
        // Packages in @types/* are known to be TypeScript declarations, so install them fully.
        return installPackageWithTypeDependencies(baseDir, spec);
    }
    // Other packages may or may not contain TypeScript declarations.
    // Download its manifest and check if it has a 'typings' or 'types' field.
    let manifest = await getFullManifest(spec);
    if (manifest.types || manifest.typings) {
        // Only do a shallow install of such packages.
        return installPackage(baseDir, spec);
    }
}

/**
 * Given the path to a package.json file (in the virtual source root) install its type-relevant dependencies.
 *
 * Note that the contents of this file have already been preprocessed by our Java counterpart.
 */
async function installDependenciesOfPackageJson(file: string, packageJson: pacote.Manifest) {
    if (packageJson == null || typeof packageJson !== 'object') return;
    let dependencyFields = ['dependencies', 'devDependencies', 'peerDependencies'];
    let promises = [];
    let baseDir = pathlib.dirname(file);
    for (let field of dependencyFields) {
        let dependencies = packageJson[field] as Record<string, string>;
        if (dependencies == null || typeof dependencies !== 'object') continue;
        for (let name of Object.getOwnPropertyNames(dependencies)) {
            if (name === 'typescript' && field !== 'dependencies') {
                // Special case: TypeScript projects generally have a devDependency on 'typescript',
                // but this is to invoke the compiler, not to interface with the API.
                // To avoid the unnecessary download, we only install typescript if it's an ordinary dependency.
                continue;
            }
            let spec = dependencies[name];
            if (typeof spec !== 'string') continue;
            let registrySpec = getRegistrySpec(name, spec);
            if (registrySpec == null) continue;
            promises.push(installIfPackageHasTypings(baseDir, registrySpec).catch(err => {
                if (err.code === 'ETARGET') {
                    console.error(`Giving up on installing '${registrySpec.raw}' as no matching version was found`);
                    // Omit the full exception as it includes the full packument and may be repeated many times.
                } else {
                    console.error(`Giving up on installing '${registrySpec.raw}' due to the following error`);
                    console.error(err);
                }
            }));
        }
    }
    return Promise.all(promises);
}

/**
 * Calls `installDependenciesOfPackageJson` with the contents of the given JSON file, or bails
 * out if the file is malformed.
 */
function installDependenciesOfPackageFile(file: string) {
    try {
        return installDependenciesOfPackageJson(file, JSON.parse(fs.readFileSync(file, 'utf-8')));
    } catch (e) {
        console.error(`Giving up on installing from '${file}' due to the following error`);
        console.error(e);
    }
}

function main() {
    let args = process.argv.slice(2);
    if (args.length === 0) {
        console.error('Usage: dependency_installer [package.json...]');
        process.exit(1);
    }
    let promises = args.map(installDependenciesOfPackageFile);
    Promise.all(promises).catch(err => {
        console.error(err);
        process.exit(1);
    });
}

main();
