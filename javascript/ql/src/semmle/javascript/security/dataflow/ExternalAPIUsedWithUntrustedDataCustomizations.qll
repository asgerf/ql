/**
 * Provides sources, sinks and sanitizers for reasoning about flow of
 * untrusted data into an external API.
 */

import javascript

module ExternalAPIUsedWithUntrustedData {
  /**
   * A data flow source for untrusted data.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for an external API function.
   */
  abstract class Sink extends DataFlow::Node {
    /**
     * Gets a human-readable name for the external API which this value flows into.
     *
     * This has the form of a pseudo-access path leading to the sink. Some ambiguity
     * is tolerated in exchange for better readability here, as the user will typically
     * have to scan over many irrelevant sinks in order to pick out the interesting ones.
     */
    abstract string getApiName();
  }

  /**
   * A sanitizer for data flowing to an external API.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  private class RemoteFlowAsSource extends Source {
    RemoteFlowAsSource() { this instanceof RemoteFlowSource }
  }

  private class LocationSource extends Source {
    LocationSource() {
      this = DOM::locationRef().getAPropertyRead(["hash", "search"])
      or
      this = DOM::locationSource()
    }
  }

  /**
   * A package name whose entire API is considered "safe" for the purpose of this query.
   */
  abstract class SafeExternalAPIPackage extends string {
    bindingset[this]
    SafeExternalAPIPackage() { any() }
  }

  /**
   * A function that is considered a "safe" external API from a security perspective.
   */
  abstract class SafeExternalAPIFunction extends API::Node { }

  /**
   * An API component that is considered "safe" from a security perspective.
   *
   * This includes all arguments passed to a `SafeExternalAPIFunction` but may be extended
   * for more fine-grained control over which APIs are considered safe.
   */
  abstract class SafeExternalApiNode extends API::Node { }

  private class DefaultSafeExternalApiNode extends SafeExternalApiNode {
    DefaultSafeExternalApiNode() {
      // Arguments to a safe function
      this = any(SafeExternalAPIFunction fn).getAParameter()
      or
      // An option passed to a safe API node
      this = any(DefaultSafeExternalApiNode fn).getAMember()
      or
      // Return value from a callback passed to a safe API node
      this = any(DefaultSafeExternalApiNode fn).getReturn()
      or
      // Value of a promise that is passed to a safe API node
      this = any(DefaultSafeExternalApiNode fn).getPromised()
    }
  }

  /**
   * A value that is treated as a generic deep object sink.
   *
   * By default, this includes the objects passed to a `PropertyProjection` or `ExtendCall`.
   *
   * Such objects tend of have lots of application-defined properties which don't represent
   * distinct API usages, so want to ensure the chain of property names isn't part of the sink name.
   */
  abstract class DeepObjectSink extends DataFlow::Node { }

  private class DefaultDeepObjectSink extends DeepObjectSink {
    DefaultDeepObjectSink() {
      this = any(PropertyProjection p).getObject()
      or
      this = any(ExtendCall c).getAnOperand()
    }
  }

  private predicate isDeepObjectSink(API::Node node) { node.getARhs() = any(DeepObjectSink deep) }

  private predicate isCommonBuiltinMethodName(string name) {
    exists(ExternalInstanceMemberDecl member |
      member.getBaseName() in ["Object", "Array", "String"] and
      name = member.getName() and
      member.getInit().(Function).getNumParameter() > 0
    )
  }

  /** Holds if data read from a use of `f` may originate from an imported package. */
  private predicate mayComeFromLibrary(API::Node f) {
    // base case: import
    exists(string path |
      f = API::moduleImport(path) and
      not path instanceof SafeExternalAPIPackage and
      // Exclude paths that can be resolved to a file in the project
      not exists(Import imprt |
        imprt.getImportedPath().getValue() = path and exists(imprt.getImportedModule())
      )
    )
    or
    // covariant recursive cases: instances, members, results, and promise contents
    // of something that comes from a library may themselves come from that library
    exists(API::Node base | mayComeFromLibrary(base) |
      f = base.getInstance() or
      f = base.getAMember() or
      f = base.getReturn() or
      f = base.getPromised()
    )
    or
    // contravariant recursive case: parameters of something that escapes to a library
    // may come from that library
    exists(API::Node base | mayEscapeToLibrary(base) | f = base.getAParameter())
  }

  /**
   * Holds if data written to a definition of `f` may flow to an imported package.
   */
  private predicate mayEscapeToLibrary(API::Node f) {
    // covariant recursive case: members, results, and promise contents of something that
    // escapes to a library may themselves escape to that library
    exists(API::Node base | mayEscapeToLibrary(base) and not isDeepObjectSink(base) |
      f = base.getAMember() or
      f = base.getReturn() or
      f = base.getPromised()
    )
    or
    // contravariant recursive case: arguments (other than the receiver) passed to a function
    // that comes from a library may escape to that library
    exists(API::Node base | mayComeFromLibrary(base) |
      f = base.getAParameter() and not f = base.getReceiver()
    )
  }

  private predicate needsPrettyName(API::Node node) {
    mayEscapeToLibrary(node) and
    exists(node.getARhs()) and
    not node instanceof SafeExternalApiNode
    or
    needsPrettyName(node.getASuccessor())
  }

  /**
   * Gets a human-readable description of the access path leading to `node`.
   */
  private string getPrettyName(API::Node node) {
    needsPrettyName(node) and
    (
      exists(string mod |
        node = API::moduleImport(mod) and
        result = mod
      )
      or
      exists(API::Node base, string basename |
        basename = getPrettyName(base) and base.getDepth() < node.getDepth()
      |
        // In practice there is no need to distinguish between 'new X' and 'X()'
        node = [base.getInstance(), base.getReturn()] and
        result = basename + "()"
        or
        mayEscapeToLibrary(base) and
        exists(string member |
          node = base.getMember(member) and
          not node = base.getUnknownMember() and
          not isNumericString(member) and
          not (member = "default" and base = API::moduleImport(_))
        |
          if member.regexpMatch("[a-zA-Z_$]\\w*")
          then result = basename + "." + member
          else result = basename + "['" + member.regexpReplaceAll("'", "\\'") + "']"
        )
        or
        mayEscapeToLibrary(base) and
        (
          node = base.getUnknownMember() or
          node = base.getMember(any(string s | isNumericString(s)))
        ) and
        result = basename + "[]"
        or
        exists(string index |
          // `getParameter(i)` requires a binding set for i, so use the raw label to get its value
          node = base.getASuccessor("parameter " + index) and
          index != "-1" and // ignore receiver
          result = basename + ".[param " + index + "]"
        )
        or
        // just collapse promises
        node = base.getPromised() and
        result = basename
      )
    )
  }

  bindingset[str]
  private predicate isNumericString(string str) { exists(str.toInt()) }

  /**
   * Holds if data written to a definition of `f` may flow to an imported package,
   * excluding cases where taint tracking would find this flow anyway, via another node
   * included in this predicate.
   *
   * For example the array `[x, y]` below is included in this predicate, but `x` and `y` are not,
   * as there are taint steps propagating them into the array literal.
   * ```js
   * require('foo').someMethod([x, y])
   * ```
   */
  private predicate mayEscapeToLibraryNotSubsumedByTaintSteps(API::Node f) {
    // covariant recursive case: members, results, and promise contents of something that
    // escapes to a library may themselves escape to that library
    exists(API::Node base | mayEscapeToLibrary(base) |
      f = base.getAMember() and not f = base.getUnknownMember()
      or
      f = base.getReturn()
    )
    or
    // contravariant recursive case: arguments (other than the receiver) passed to a function
    // that comes from a library may escape to that library
    exists(API::Node base | mayComeFromLibrary(base) |
      f = base.getAParameter() and not f = base.getReceiver()
    )
  }

  private class ExternalApiSink extends Sink {
    API::Node api;

    ExternalApiSink() {
      this = api.getARhs() and
      mayEscapeToLibraryNotSubsumedByTaintSteps(api) and
      not api instanceof SafeExternalApiNode and
      // Ignore arguments to a method such as 'indexOf' that's likely called on a string or array value
      not this =
        any(DataFlow::CallNode call | isCommonBuiltinMethodName(call.getCalleeName()))
            .getAnArgument()
    }

    override string getApiName() { result = getPrettyName(api) }
  }
}
