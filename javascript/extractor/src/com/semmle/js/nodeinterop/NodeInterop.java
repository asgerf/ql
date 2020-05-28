package com.semmle.js.nodeinterop;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;

import com.semmle.js.extractor.EnvironmentVariables;
import com.semmle.ts.extractor.TypeScriptParser;
import com.semmle.util.exception.CatastrophicError;
import com.semmle.util.exception.Exceptions;
import com.semmle.util.exception.InterruptedError;
import com.semmle.util.exception.ResourceError;
import com.semmle.util.exception.UserError;
import com.semmle.util.process.Env;

/**
 * Methods for interacting with a Node.js process.
 *
 * Note that most environment variables are named "TYPESCRIPT" for legacy reasons and remain
 * this way for backwards compatibility.
 */
public class NodeInterop {
  /**
   * An environment variable that can be set to specify a timeout to use when verifying the
   * TypeScript installation, in milliseconds. Default is 10000.
   */
  public static final String TYPESCRIPT_TIMEOUT_VAR = "SEMMLE_TYPESCRIPT_TIMEOUT";

  /**
   * An environment variable that can be set to indicate the location of the Node.js runtime, as an
   * alternative to adding Node to the PATH.
   */
  public static final String TYPESCRIPT_NODE_RUNTIME_VAR = "SEMMLE_TYPESCRIPT_NODE_RUNTIME";

  /**
   * An environment variable that can be set to provide additional arguments to the Node.js runtime
   * each time it is invoked. Arguments should be separated by spaces.
   */
  public static final String TYPESCRIPT_NODE_RUNTIME_EXTRA_ARGS_VAR =
      "SEMMLE_TYPESCRIPT_NODE_RUNTIME_EXTRA_ARGS";

  /**
   * An environment variable that can be set to specify a number of retries when verifying
   * the TypeScript installation. Default is 3.
   */
  public static final String TYPESCRIPT_RETRIES_VAR = "SEMMLE_TYPESCRIPT_RETRIES";

  private static String nodeJsVersionString;

  /**
   * Arguments to pass to the Node.js runtime each time it is invoked. Initialised by {@link
   * #getNodeJsRuntimeExtraArgs}.
   */
  private static List<String> _nodeJsRuntimeExtraArgs;

  /**
   * Returns the folder containing our bundled Node.js scripts.
   */
  public static File getBundledScriptFolder() {
    // This folder is called typescript-parser-wrapper for legacy reasons, but we use
    // it more generally now.
    return new File(EnvironmentVariables.getExtractorRoot(), "tools/typescript-parser-wrapper");
  }

  /** Gets the command to run to invoke `node`. */
  private static String getNodeJsRuntime() {
    String explicitNodeJsRuntime = Env.systemEnv().get(TYPESCRIPT_NODE_RUNTIME_VAR);
    if (explicitNodeJsRuntime != null) {
      // Use the specified Node.js executable.
      return explicitNodeJsRuntime;
    } else {
      // Look for `node` on the PATH.
      return "node";
    }
  }

  /** Gets any extra arguments to use when invoking `node`. */
  private static List<String> getNodeJsRuntimeExtraArgs() {
    if (_nodeJsRuntimeExtraArgs != null) return _nodeJsRuntimeExtraArgs;
    // Determine any additional arguments to be passed to Node.js each time it's called.
    String extraArgs = Env.systemEnv().get(TYPESCRIPT_NODE_RUNTIME_EXTRA_ARGS_VAR);
    if (extraArgs != null) {
      _nodeJsRuntimeExtraArgs = Arrays.asList(extraArgs.split("\\s+"));
    } else {
      _nodeJsRuntimeExtraArgs = Collections.emptyList();
    }
    return _nodeJsRuntimeExtraArgs;
  }

  /**
   * Verifies that Node.js is installed and throws an exception otherwise.
   *
   * @param verbose if true, log the Node.js executable path, version strings, and any additional
   *     arguments.
   */
  public static void verifyInstallation(boolean verbose) {
    verifyNodeInstallation();
    if (verbose) {
      System.out.println("Found Node.js at: " + getNodeJsRuntime());
      System.out.println("Found Node.js version: " + nodeJsVersionString);
      List<String> nodeJsRuntimeExtraArgs = getNodeJsRuntimeExtraArgs();
      if (!nodeJsRuntimeExtraArgs.isEmpty()) {
        System.out.println("Additional arguments for Node.js: " + nodeJsRuntimeExtraArgs);
      }
    }
  }

  /** Checks that Node.js is installed and can be run and returns its version string. */
  public static String verifyNodeInstallation() {
    if (nodeJsVersionString != null) return nodeJsVersionString;

    // Run 'node --version' with a timeout, and retry a few times if it times out.
    return withRetries(NodeInterop::startNodeAndGetVersion, "Node.js");
  }

  /**
   * Returns the timeout in milliseconds when probing a Node installation.
   */
  public static long getTimeout() {
    return Env.systemEnv().getInt(TYPESCRIPT_TIMEOUT_VAR, 10000);
  }

  /**
   * Returns the number of times to retry a command when probing a Node installation.
   */
  public static int getNumberOfRetries() {
    return Env.systemEnv().getInt(TYPESCRIPT_RETRIES_VAR, 3);
  }

  /**
   * Executes the given callback and retries it if it times out.
   * <p>
   * If the Java process is suspended we may get a spurious timeout, and we want to
   * support long suspensions in cloud environments. Instead of setting a huge timeout,
   * retrying guarantees we can survive arbitrary suspensions as long as they don't happen
   * too many times in rapid succession.
   */
  public static <T> T withRetries(Supplier<T> callback, String name) {
    int numRetries = getNumberOfRetries();
    for (int i = 0; i < numRetries - 1; ++i) {
      try {
        return callback.get();
      } catch (InterruptedError e) {
        Exceptions.ignore(e, "We will retry the call that caused this exception.");
        System.err.println("Starting " + name + " seems to take a long time. Retrying.");
      }
    }
    try {
      return callback.get();
    } catch (InterruptedError e) {
      Exceptions.ignore(e, "Exception details are not important.");
      throw new CatastrophicError(
          "Could not start " + name + " (timed out after " + (getTimeout() / 1000) + "s and " + numRetries + " attempts");
    }
  }

  /**
   * Checks that Node.js is installed and can be run and returns its version string.
   */
  private static String startNodeAndGetVersion() throws InterruptedError {
    FireAndForgetProcess process = new FireAndForgetProcess(getNodeJsRuntimeInvocation("--version"));
    
    try {
      return process.execute();
    } catch (ProcessFailedError err) {
      // If 'node' was found but failed somehow, treat as a catastrophic error.
      throw new CatastrophicError(
          "Could not start Node.js. It is required for TypeScript extraction.", err);
    } catch (ResourceError err) {
      // If 'node' could not be found, convert this to a UserError.
      throw new UserError(
          "Could not start Node.js. It is required for TypeScript extraction."
              + "\nPlease install Node.js and ensure 'node' is on the PATH.");
    }
  }

  /**
   * Gets a command line to invoke the Node.js runtime. Any arguments in {@link
   * TypeScriptParser#nodeJsRuntimeExtraArgs} are passed first, followed by those in {@code args}.
   */
  public static List<String> getNodeJsRuntimeInvocation(String... args) {
    List<String> result = new ArrayList<>();
    result.add(getNodeJsRuntime());
    result.addAll(getNodeJsRuntimeExtraArgs());
    for (String arg : args) {
      result.add(arg);
    }
    return result;
  }
}
