/**
 * Provides classes and predicates for reasoning about data flow through the redux package.
 */

import javascript

// The core Redux model contributes two kinds of steps:
//   1. From dispatch argument to reducer parameter ("dispatch step")
//   2. From reducer return-value to state access ("reducer step")
//
// A third kind of step is also needed to adapter libraries like `react-redux`, for example:
//   3. From mapStateToProps return-value to props access in react component
//
// The third kind of step is technically independent of the core Redux library, but
// this file includes modeling of such adapter libraries as well.
//
// The first step, from dispatch to reducer, has to deal with type tags, so it can't always
// map to a function parameter.
module Redux {
  private class ReduxRootStateTag extends DataFlow::CustomNodes::SingletonNodeTag {
    ReduxRootStateTag() { this = "redux-root-state" }
  }

  private class ReduxRootStateNode extends DataFlow::CustomNodes::SingletonNode,
    DataFlow::SourceNode::Range {
    override ReduxRootStateTag tag;
  }

  private ReduxRootStateNode rootState() { any() }

  /** An API node referring to the root state. */
  abstract private class RootStateNode extends API::Node { }

  /** Gets an API node corresponding to an access of `prop` on the root state. */
  pragma[noinline]
  private API::Node rootStateProp(string prop) { result = any(RootStateNode n).getMember(prop) }

  /**
   * Gets a node interprocedurally reachable from `source`, where `source` must be known
   * to have a corresponding use-node in the API graph.
   *
   * We use this to maintain a consistent interface based on data-flow nodes, while being
   * able to reuse the type-tracking done by API graphs in cases where the node is known to
   * be part of the API graph.
   */
  pragma[inline]
  private DataFlow::SourceNode getAnApiReference(DataFlow::SourceNode source) {
    exists(API::Node apiNode |
      apiNode.getAnImmediateUse() = source and
      result = apiNode.getAUse()
    )
  }

  class StoreCreation extends DataFlow::SourceNode {
    StoreCreation::Range range;

    StoreCreation() { this = range }

    /** Gets a reference to the store. */
    DataFlow::SourceNode ref() { result = getAnApiReference(this) }

    /** Gets the data flow node holding the root reducer for this store. */
    DataFlow::Node getReducerArg() { result = range.getReducerArg() }

    /** Gets a data flow node referring to the root reducer. */
    DataFlow::SourceNode getAReducerSource() { result = getReducerArg().(ReducerArg).getASource() }
  }

  module StoreCreation {
    abstract class Range extends DataFlow::SourceNode {
      abstract DataFlow::Node getReducerArg();
    }

    private class CreateStore extends DataFlow::CallNode, Range {
      CreateStore() { this = API::moduleImport("redux").getMember("createStore").getACall() }

      override DataFlow::Node getReducerArg() { result = getArgument(0) }
    }

    private class ToolkitStore extends API::CallNode, Range {
      ToolkitStore() {
        this = API::moduleImport("@reduxjs/toolkit").getMember("configureStore").getACall()
      }

      override DataFlow::Node getReducerArg() {
        result = getParameter(0).getMember("reducer").getARhs()
      }
    }
  }

  /** A data flow node that is used as a reducer. */
  private class ReducerArg extends DataFlow::Node {
    ReducerArg() {
      this = any(StoreCreation c).getReducerArg()
      or
      this = any(DelegatingReducer r).getStateHandlerArg(_)
      or
      this = any(DelegatingReducer r).getTypeTagHandlerArg(_, _)
    }

    /** Gets a data flow node that flows to this reducer argument. */
    DataFlow::SourceNode getASource(DataFlow::TypeBackTracker t) {
      t.start() and
      result = getALocalSource()
      or
      exists(DataFlow::Node mid | result.flowsTo(mid) |
        // Step through forwarding functions
        DataFlow::functionForwardingStep(mid, getASource(t.continue()))
        or
        exists(
          API::CallNode call // TODO: make identity-reducer step extensibble
        |
          call = API::moduleImport("redux-persist").getMember("persistReducer").getACall() and
          getASource(t.continue()) = call and
          mid = call.getArgument(1)
        )
        or
        // Step through function composition (usually composed with various state "enhancer" functions)
        exists(FunctionCompositionCall compose, DataFlow::CallNode call |
          call = compose.getACall() and
          getASource(t.continue()) = call and
          mid = [compose.getAnOperandNode(), call.getAnArgument()]
        )
      )
      or
      exists(DataFlow::TypeBackTracker t2 | result = getASource(t2).backtrack(t2, t))
    }

    /** Gets a data flow node that flows to this reducer argument. */
    DataFlow::SourceNode getASource() { result = getASource(DataFlow::TypeBackTracker::end()) }

    /**
     * Holds if the actions dispatched to this reducer have the property `propName` set to `propValue`.
     */
    predicate isTypeTagHandler(string propName, string propValue) {
      exists(DelegatingReducer r |
        this = r.getTypeTagHandlerArg(propName, propValue)
        or
        this = r.getStateHandlerArg(_) and
        r.getUseSite().isTypeTagHandler(propName, propValue)
      )
    }

    /**
     * Holds if this reducer operates on the root state, as opposed to some access path within the state.
     */
    predicate isRootStateHandler() {
      this = any(StoreCreation c).getReducerArg()
      or
      exists(DelegatingReducer r |
        this = r.getTypeTagHandlerArg(_, _) and
        r.getUseSite().isRootStateHandler()
      )
    }

    /**
     * Gets an API node corresponding to the access path within the state returned by this reducer.
     *
     * Has no result for root reducers; those are special-cased in `getAffectedStateNode`.
     */
    private API::Node getAnAffectedStateApiNode() {
      exists(DelegatingReducer r |
        this = r.getTypeTagHandlerArg(_, _) and
        result = r.getUseSite().getAnAffectedStateApiNode()
        or
        exists(string prop | this = r.getStateHandlerArg(prop) |
          result = r.getUseSite().getAnAffectedStateApiNode().getMember(prop)
          or
          r.getUseSite().isRootStateHandler() and
          result = rootStateProp(prop)
        )
      )
    }

    /**
     * Gets a state access affected by the return value of this reducer.
     */
    DataFlow::SourceNode getAnAffectedStateNode() {
      result = getAnAffectedStateApiNode().getAnImmediateUse()
      or
      isRootStateHandler() and
      result = rootState()
    }
  }

  abstract class DelegatingReducer extends DataFlow::SourceNode {
    DataFlow::Node getStateHandlerArg(string prop) { none() }

    DataFlow::Node getTypeTagHandlerArg(string propName, string propValue) { none() }

    /** Gets the use site of this reducer. */
    final ReducerArg getUseSite() { result.getASource() = this }
  }

  predicate unconnectedReducer(DelegatingReducer r) {
    // Findings:
    //   'workspaceReducer' in graphql-playground: manually invoked with state.getIn(['workspace', blah])
    not exists(r.getUseSite())
  }

  private class CombineReducers extends API::CallNode, DelegatingReducer {
    CombineReducers() {
      this = API::moduleImport(["redux", "redux-immutable"]).getMember("combineReducers").getACall()
    }

    override DataFlow::Node getStateHandlerArg(string prop) {
      // TODO: nested reducers
      result = getParameter(0).getMember(prop).getARhs()
    }
  }

  private class HandleActions extends API::CallNode, DelegatingReducer {
    HandleActions() {
      this = API::moduleImport("redux-actions").getMember("handleActions").getACall()
    }

    override DataFlow::Node getTypeTagHandlerArg(string propName, string propValue) {
      result = getParameter(0).getMember(propValue).getARhs() and
      propName = "type"
    }
  }

  /**
   * A source of the `dispatch` function, used as starting point for `getADispatchFunctionReference`.
   */
  abstract private class DispatchFunctionSource extends DataFlow::SourceNode { }

  /**
   * A value that is dispatched, that is, flows to the first argument of `dispatch`
   * (but where the call itself may or may not be seen).
   *
   * Used as starting point for `getADispatchedValueSource`.
   */
  abstract private class DispatchedValueSink extends DataFlow::Node { }

  private class StoreDispatchSource extends DispatchFunctionSource {
    StoreDispatchSource() { this = any(StoreCreation c).ref().getAPropertyRead("dispatch") }
  }

  /** Gets a data flow node referring to a thing. */
  private DataFlow::SourceNode getADispatchFunctionReference(DataFlow::TypeTracker t) {
    t.start() and
    result instanceof DispatchFunctionSource
    or
    // When using the redux-thunk middleware, dispatching a function value results in that
    // function being invoked with (dispatch, getState).
    // We simply assume redux-thunk middleware is always installed.
    t.start() and
    result = getADispatchedValueSource().(DataFlow::FunctionNode).getParameter(0)
    or
    exists(DataFlow::TypeTracker t2 | result = getADispatchFunctionReference(t2).track(t2, t))
  }

  /** Gets a data flow node referring to a thing. */
  DataFlow::SourceNode getADispatchFunctionReference() {
    result = getADispatchFunctionReference(DataFlow::TypeTracker::end())
  }

  /** Gets a data flow node referring to a thing. */
  private DataFlow::SourceNode getADispatchedValueSource(DataFlow::TypeBackTracker t) {
    t.start() and
    result = any(DispatchedValueSink d).getALocalSource()
    or
    t.start() and
    result = getADispatchFunctionReference().getACall().getArgument(0).getALocalSource()
    or
    exists(DataFlow::TypeBackTracker t2 | result = getADispatchedValueSource(t2).backtrack(t2, t))
  }

  /** Gets a data flow node referring to a thing. */
  DataFlow::SourceNode getADispatchedValueSource() {
    result = getADispatchedValueSource(DataFlow::TypeBackTracker::end())
  }

  predicate missedDispatch(DataFlow::SourceNode node) {
    // Many originally missed in grafana due to thunks in mapDispatchToProps functions, but found now
    // Still missing navigateToExplore due to: possibly unresolved import?
    node.asExpr().(Identifier).getName() = "dispatch" and
    not node = getADispatchFunctionReference()
  }

  // React-redux model
  private module ReactRedux {
    API::Node useSelector() { result = API::moduleImport("react-redux").getMember("useSelector") }

    /**
     * Step out of a `useSelector` call, such as from `state.x` to the result of `useSelector(state => state.x)`.
     */
    class UseSelectorStep extends API::CallNode, DataFlow::AdditionalFlowStep {
      UseSelectorStep() { this = useSelector().getACall() }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        pred = getParameter(0).getReturn().getARhs() and
        succ = this
      }
    }

    /** The argument to a `useSelector` callback, seen as a root state reference. */
    class UseSelectorStateSource extends RootStateNode {
      UseSelectorStateSource() { this = useSelector().getParameter(0).getParameter(0) }
    }

    private class RealConnectFunction extends ConnectCall {
      RealConnectFunction() {
        this = API::moduleImport("react-redux").getMember("connect").getACall()
      }

      override API::Node getMapStateToProps() { result = getParameter(0) }

      override API::Node getMapDispatchToProps() { result = getParameter(1) }
    }

    private DataFlow::CallNode heuristicConnectCall() {
      result.getAnArgument().asExpr().(Identifier).getName() =
        ["mapStateToProps", "mapDispatchToProps"] and
      not result = DataFlow::moduleMember("react-redux", "connect").getACall() // exclude genuine calls to avoid duplicate tuples
    }

    /**
     * An entry point in the API graphs corresponding to functions named `mapDispatchToProps`,
     * used to catch cases where the call to `connect` was not found (usually because of it being
     * wrapped in another function, which API graphs won't look through).
     */
    private class HeuristicConnectEntryPoint extends API::EntryPoint {
      HeuristicConnectEntryPoint() { this = "react-redux-connect" }

      override DataFlow::Node getARhs() { none() }

      override DataFlow::SourceNode getAUse() {
        result = heuristicConnectCall().getCalleeNode().getALocalSource()
      }
    }

    private class HeuristicConnectFunction extends ConnectCall {
      HeuristicConnectFunction() {
        this = API::root().getASuccessor(any(HeuristicConnectEntryPoint e)).getACall()
      }

      override API::Node getMapStateToProps() {
        result = getAParameter() and
        result.getARhs().asExpr().(Identifier).getName() = "mapStateToProps"
      }

      override API::Node getMapDispatchToProps() {
        result = getAParameter() and
        result.getARhs().asExpr().(Identifier).getName() = "mapDispatchToProps"
      }
    }

    /**
     * A call to `connect()`, typically as part of a code pattern like the following:
     * ```js
     * let withConnect = connect(mapStateToProps, mapDispatchToProps);
     * let MyAwesomeComponent = compose(withConnect, otherStuff)(MyComponent);
     * ```
     */
    abstract private class ConnectCall extends API::CallNode {
      abstract API::Node getMapStateToProps();

      abstract API::Node getMapDispatchToProps();

      /**
       * Gets a function whose first argument becomes the React component to connect.
       */
      DataFlow::SourceNode getAComponentTransformer() {
        result = this
        or
        exists(FunctionCompositionCall compose |
          getAComponentTransformer().flowsTo(compose.getAnOperandNode()) and
          result = compose
        )
      }

      /**
       * Gets a data-flow node that should flow to `props.name` via the `mapDispatchToProps` function.
       */
      DataFlow::Node getDispatchPropNode(string name) {
        // TODO not currently used
        result = getMapDispatchToProps().getMember(name).getARhs()
        or
        exists(DataFlow::CallNode bind |
          bind = API::moduleImport("redux").getMember("bindActionCreators").getACall() and
          bind.flowsTo(getMapDispatchToProps().getReturn().getARhs()) and
          result = bind.getOptionArgument(0, name)
        )
      }

      /**
       * Gets the React component decorated by this call, if one can be determined.
       */
      ReactComponent getReactComponent() {
        result
            .getAComponentCreatorReference()
            .flowsTo(getAComponentTransformer().getACall().getArgument(0))
      }
    }

    private class ConnectionStep extends DataFlow::AdditionalFlowStep {
      ConnectionStep() { this instanceof ConnectCall }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        exists(ConnectCall connect | connect = this |
          pred = connect.getMapStateToProps().getReturn().getARhs() and
          succ = connect.getReactComponent().getADirectPropsAccess()
          or
          // Boost property depth tracking
          exists(string name |
            pred = connect.getMapStateToProps().getReturn().getMember(name).getARhs() and
            succ = connect.getReactComponent().getAPropRead(name)
          )
        )
      }
    }

    private class MapDispatchToPropsArg extends DispatchFunctionSource {
      MapDispatchToPropsArg() {
        // If `mapDispatchToProps` is a function, its first argument is `dispatch`
        this = any(ConnectCall c).getMapDispatchToProps().getParameter(0).getAnImmediateUse()
      }
    }

    private class MapDispatchToPropsMember extends DispatchedValueSink {
      MapDispatchToPropsMember() {
        // If `mapDispatchToProps` is an object, each method will have its result dispatched
        this = any(ConnectCall c).getMapDispatchToProps().getAMember().getReturn().getARhs()
      }
    }
    // TODO: contribute step to dispatch flow
    // private class ReduxToolkitDispatch extends Dispatcher {
    //   override DataFlow::CallNode getAnAdditionalDispatchInvocation() {
    //     exists(ConnectCall call, string name |
    //       ref().flowsTo(call.getDispatchPropNode(name)) and
    //       result = call.getReactComponent().getAPropRead(name).getACall()
    //     )
    //   }
    // }
  }

  module Reselect {
    class CreateSelectorCall extends API::CallNode {
      CreateSelectorCall() {
        this = API::moduleImport("reselect").getMember("createSelector").getACall()
      }

      API::Node getSelectorFunction(int i) {
        // When there are multiple callbacks, exclude the last one
        result = getParameter(i) and
        (i = 0 or i < getNumArgument() - 1)
        or
        exists(DataFlow::ArrayCreationNode array |
          array.flowsTo(getArgument(0)) and
          result.getAUse() = array.getElement(i)
        )
      }
    }

    /** The state argument to a selector */
    private class SelectorStateArg extends RootStateNode {
      SelectorStateArg() { this = any(CreateSelectorCall c).getSelectorFunction(_).getParameter(0) }
    }

    predicate selectorStep(DataFlow::Node pred, DataFlow::Node succ) {
      // Return value of `i`th callback flows to the `i`th parameter of the last callback.
      exists(CreateSelectorCall call, int index |
        call.getNumArgument() > 1 and
        pred = call.getSelectorFunction(index).getReturn().getARhs() and
        succ = call.getLastParameter().getParameter(index).getAnImmediateUse()
      )
      or
      // The result of the last callback is the final result
      exists(CreateSelectorCall call |
        pred = call.getLastParameter().getReturn().getARhs() and
        succ = call
      )
    }

    class SelectorStep extends DataFlow::AdditionalFlowStep {
      SelectorStep() { selectorStep(_, this) }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        selectorStep(pred, succ) and
        this = succ
      }
    }
  }
}
