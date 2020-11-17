/**
 * Provides a taint tracking configuration for reasoning about file
 * data in outbound network requests.
 *
 * Note, for performance reasons: only import this file if
 * `FileAccessToHttp::Configuration` is needed, otherwise
 * `FileAccessToHttpCustomizations` should be imported instead.
 */

import javascript

module ExternalAPIUsedWithUntrustedData {
  import ExternalAPIUsedWithUntrustedDataCustomizations::ExternalAPIUsedWithUntrustedData

  /** Flow label for objects from which a tainted value is reachable. */
  private class ObjectWrapperFlowLabel extends DataFlow::FlowLabel {
    ObjectWrapperFlowLabel() {
      exists(DeepObjectSink sink) and
      this = "object-wrapper"
    }
  }

  /**
   * A taint tracking configuration for untrusted data flowing to an external API.
   */
  class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "ExternalAPIUsedWithUntrustedData" }

    override predicate isSource(DataFlow::Node source) { source instanceof Source }

    override predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel lbl) {
      sink instanceof Sink
      or
      sink instanceof DeepObjectSink and
      lbl instanceof ObjectWrapperFlowLabel
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }

    override predicate isAdditionalFlowStep(
      DataFlow::Node pred, DataFlow::Node succ, DataFlow::FlowLabel predLbl,
      DataFlow::FlowLabel succLbl
    ) {
      exists(DataFlow::PropWrite write |
        pred = write.getRhs() and
        succ = write.getBase().getALocalSource() and
        (predLbl.isTaint() or predLbl instanceof ObjectWrapperFlowLabel) and
        succLbl instanceof ObjectWrapperFlowLabel
      )
    }

    override predicate isSanitizerEdge(DataFlow::Node pred, DataFlow::Node succ) {
      // Block flow from the location to its properties, as the relevant properties (hash and search) are taint sources of their own.
      // The location source is only used for propagating through API calls like `new URL(location)` and into external APIs where
      // the whole location object escapes.
      exists(DataFlow::PropRead read |
        read = DOM::locationRef().getAPropertyRead() and
        pred = read.getBase() and
        succ = read
      )
    }
  }

  /** A node representing data being passed to an external API. */
  class ExternalAPIDataNode extends DataFlow::Node {
    ExternalAPIDataNode() { this instanceof Sink }
  }

  /** A node representing untrusted data being passed to an external API. */
  class UntrustedExternalAPIDataNode extends ExternalAPIDataNode {
    UntrustedExternalAPIDataNode() { any(Configuration c).hasFlow(_, this) }

    /** Gets a source of untrusted data which is passed to this external API data node. */
    DataFlow::Node getAnUntrustedSource() { any(Configuration c).hasFlow(result, this) }
  }

  /**
   * Name of an external API sink, boxed in a newtype for consistency with other languages.
   */
  private newtype TExternalApi =
    MkExternalApiNode(string name) {
      exists(Sink sink |
        any(Configuration c).hasFlow(_, sink) and
        name = sink.getApiName()
      )
    }

  /** An external API which is used with untrusted data. */
  class ExternalAPIUsedWithUntrustedData extends TExternalApi {
    /** Gets a possibly untrusted use of this external API. */
    UntrustedExternalAPIDataNode getUntrustedDataNode() {
      this = MkExternalApiNode(result.(Sink).getApiName())
    }

    /** Gets the number of untrusted sources used with this external API. */
    int getNumberOfUntrustedSources() {
      result = count(getUntrustedDataNode().getAnUntrustedSource())
    }

    /** Gets a textual representation of this element. */
    string toString() { this = MkExternalApiNode(result) }
  }
}
