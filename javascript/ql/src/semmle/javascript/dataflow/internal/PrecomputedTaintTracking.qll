private import javascript
private import FlowSteps

module PrecomputedTaint {
  predicate isSource(DataFlow::Node node) {
    node instanceof RemoteFlowSource
  }

  /**
   * Holds if there is a flow step from `pred` to `succ` described by `summary`
   * under configuration `cfg`, disregarding barriers.
   *
   * Summary steps through function calls are not taken into account.
   */
  pragma[inline]
  private predicate basicFlowStepNoBarrier(
    DataFlow::Node pred, DataFlow::Node succ
  ) {
    // --- basicFlowStepNoBarrier ---

    // Local flow [inlined below]
    // exists(FlowLabel predlbl, FlowLabel succlbl |
    //   localFlowStep(pred, succ, cfg, predlbl, succlbl)
    // )
    // or

    // Flow through properties of objects
    propertyFlowStep(pred, succ)
    or
    // Flow through global variables
    globalFlowStep(pred, succ)
    or
    // Flow into function
    callStep(pred, succ)
    or
    // Flow out of function
    returnStep(pred, succ)
    or
    // --- localFlowStep ---
    pred = succ.getAPredecessor()
    or
    any(DataFlow::AdditionalFlowStep afs).step(pred, succ)
    or
    any(DataFlow::AdditionalFlowStep afs).step(pred, succ, _, _)
    or
    any(TaintTracking::AdditionalTaintStep st).step(pred, succ)
    or
    localExceptionStep(pred, succ)
  }

  private predicate isAdditionalLoadStep(
    DataFlow::Node pred, DataFlow::Node succ, string prop
  ) {
    any(AdditionalFlowStep s).loadStep(pred, succ, prop)
  }

  private predicate isAdditionalStoreStep(
    DataFlow::Node pred, DataFlow::Node succ, string prop
  ) {
    any(AdditionalFlowStep s).storeStep(pred, succ, prop)
  }

  private predicate isAdditionalLoadStoreStep(
    DataFlow::Node pred, DataFlow::Node succ, string loadProp, string storeProp
  ) {
    any(AdditionalFlowStep s).loadStoreStep(pred, succ, loadProp, storeProp)
    or
    loadProp = storeProp and
    any(AdditionalFlowStep s).loadStoreStep(pred, succ, loadProp)
  }

  /**
   * Holds if there exists a load-step from `pred` to `succ` under configuration `cfg`,
   * and the forwards exploratory flow has found a relevant store-step with the same property as the load-step.
   */
  private predicate exploratoryLoadStep(
    DataFlow::Node pred, DataFlow::Node succ
  ) {
    exists(string prop | prop = getAForwardRelevantLoadProperty() |
      isAdditionalLoadStep(pred, succ, prop)
      or
      basicLoadStep(pred, succ, prop)
    )
  }

  /**
   * Gets a property where the forwards exploratory flow has found a relevant store-step with that property.
   * The property is therefore relevant for load-steps in the forward exploratory flow.
   *
   * This private predicate is only used in `exploratoryLoadStep`, and exists as a separate predicate to give the compiler a hint about join-ordering.
   */
  private string getAForwardRelevantLoadProperty() {
    exists(DataFlow::Node previous | isRelevantForward(previous) |
      basicStoreStep(previous, _, result) or
      isAdditionalStoreStep(previous, _, result)
    )
    or
    result = getAPropertyUsedInLoadStore()
  }

  /**
   * Gets a property that is used in an `additionalLoadStoreStep` where the loaded and stored property are not the same.
   *
   * The properties from this predicate are used as a white-list of properties for load/store steps that should always be considered in the exploratory flow.
   */
  private string getAPropertyUsedInLoadStore() {
    exists(string loadProp, string storeProp |
      isAdditionalLoadStoreStep(_, _, loadProp, storeProp) and
      storeProp != loadProp and
      result = [storeProp, loadProp]
    )
  }

  pragma[inline]
  private predicate exploratoryFlowStep(
    DataFlow::Node pred, DataFlow::Node succ
  ) {
    basicFlowStepNoBarrier(pred, succ) or
    exploratoryLoadStep(pred, succ) or
    isAdditionalLoadStoreStep(pred, succ, _, _) or
    // the following three disjuncts taken together over-approximate flow through
    // higher-order calls
    callback(pred, succ) or
    succ = pred.(DataFlow::FunctionNode).getAParameter() or
    exploratoryBoundInvokeStep(pred, succ)
  }

  /**
   * Holds if there exists a store-step from `pred` to `succ` under configuration `cfg`,
   * and somewhere in the program there exists a load-step that could possibly read the stored value.
   */
  private predicate exploratoryForwardStoreStep(
    DataFlow::Node pred, DataFlow::Node succ
  ) {
    exists(string prop |
      basicLoadStep(_, _, prop) or
      isAdditionalLoadStep(_, _, prop) or
      prop = getAPropertyUsedInLoadStore()
    |
      isAdditionalStoreStep(pred, succ, prop) or
      basicStoreStep(pred, succ, prop)
    )
  }

  /**
   * Holds if `nd` may be reachable from a source under `cfg`.
   *
   * No call/return matching is done, so this is a relatively coarse over-approximation.
   */
  cached
  predicate isRelevantForward(DataFlow::Node nd) {
    isSource(nd)
    or
    exists(DataFlow::Node mid | isRelevantForward(mid) |
      exploratoryFlowStep(mid, nd) or
      exploratoryForwardStoreStep(mid, nd)
    )
  }

  pragma[inline]
  DataFlow::Node getATaintedNode() {
    isRelevantForward(result)
  }

  pragma[inline]
  DataFlow::Node getAnUnseenNode() {
    not isRelevantForward(result)
  }
}
