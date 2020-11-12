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

// TODO: typescript-fsa family of packages
// TODO: handle immer-style `state.foo = foo` assignments in reducer; add steps back to state access paths

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
      CreateStore() { this = API::moduleImport(["redux", "@reduxjs/toolkit"]).getMember("createStore").getACall() }

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
      this = any(DelegatingReducer r).getTypeTagHandlerArg(_)
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
        // Step through library functions like `redux-persist`
        mid = getASource(t.continue()).(DelegatingReducer).getAPlainHandlerArg()
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
     * Holds if the actions dispatched to this reducer have the property `type` set to `propValue`.
     */
    predicate isTypeTagHandler(string propValue) {
      exists(DelegatingReducer r |
        this = r.getTypeTagHandlerArg(propValue)
        or
        this = r.getStateHandlerArg(_) and
        r.getUseSite().isTypeTagHandler(propValue)
      )
    }

    /**
     * Holds if this reducer operates on the root state, as opposed to some access path within the state.
     */
    predicate isRootStateHandler() {
      this = any(StoreCreation c).getReducerArg()
      or
      exists(DelegatingReducer r |
        this = r.getTypeTagHandlerArg(_) and
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
        this = r.getTypeTagHandlerArg(_) and
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

    /**
     * Gets a data flow node holding a reducer to which this one forwards its arguments when
     * `action.type = propValue`.
     *
     * TODO: Is the action going to be the action `payload` or the raw action?
     */
    DataFlow::Node getTypeTagHandlerArg(string propValue) { none() }

    /**
     * Gets a data flow node holding a reducer to which this one forwards every (state, action) pair
     * (for the purposes of this model).
     */
    DataFlow::Node getAPlainHandlerArg() { none() }

    /** Gets the use site of this reducer. */
    final ReducerArg getUseSite() { result.getASource() = this }
  }

  private class CombineReducers extends API::CallNode, DelegatingReducer {
    CombineReducers() {
      this = API::moduleImport(["redux", "redux-immutable", "@reduxjs/toolkit"]).getMember("combineReducers").getACall()
    }

    override DataFlow::Node getStateHandlerArg(string prop) {
      // TODO: nested reducers
      result = getParameter(0).getMember(prop).getARhs()
    }
  }

  private API::Node reduxActionsLike() {
    result = API::moduleImport(["redux-actions", "redux-ts-utils"])
  }

  /**
   * Gets the type tag of an action creator reaching `node`, or the type tag from one of the action
   * types passed to a `combineActions` call reaching `node`.
   */
  private string getAnActionTypeTag(DataFlow::SourceNode node) {
    exists(ActionCreator action |
      node = action.ref() and
      result = action.getTypeTag()
    )
    or
    exists(API::CallNode combiner |
      combiner = reduxActionsLike().getMember("combineActions").getACall() and
      node = combiner.getReturn().getAUse() and
      (
        combiner.getAnArgument().mayHaveStringValue(result)
        or
        result = getAnActionTypeTag(combiner.getAnArgument().getALocalSource())
      )
    )
  }

  /** Gets the type tag of an action reaching `node`, or the string value of `node`. */
  pragma[inline] // Inlined to avoid duplicating `mayHaveStringValue`
  private string getATypeTagFromNode(DataFlow::Node node) {
    node.mayHaveStringValue(result)
    or
    result = getAnActionTypeTag(node.getALocalSource())
  }

  private class HandleActions extends API::CallNode, DelegatingReducer {
    HandleActions() {
      this = reduxActionsLike().getMember("handleActions").getACall()
    }

    override DataFlow::Node getTypeTagHandlerArg(string propValue) {
      result = getParameter(0).getMember(propValue).getARhs()
      or
      // The property name may be the result of `combineActions`:
      //
      //   { [combineActions(a1, a2)]: (state, action) => { ... }}
      //
      exists(DataFlow::PropWrite write |
        write = getParameter(0).getARhs().getALocalSource().getAPropertyWrite() and
        propValue = getAnActionTypeTag(write.getPropertyNameExpr().flow().getALocalSource()) and
        result = write.getRhs()
      )
    }
  }

  private class HandleAction extends API::CallNode, DelegatingReducer {
    HandleAction() {
      this = reduxActionsLike().getMember("handleAction").getACall()
    }

    override DataFlow::Node getTypeTagHandlerArg(string propValue) {
      result = getArgument(1) and
      propValue = getATypeTagFromNode(getArgument(0))
    }
  }

  private class PersistReducer extends DataFlow::CallNode, DelegatingReducer {
    PersistReducer() {
      this = API::moduleImport("redux-persist").getMember("persistReducer").getACall()
    }

    override DataFlow::Node getAPlainHandlerArg() {
      result = getArgument(1)
    }
  }

  /**
   * Model `reduce-reducers` as a reducer that dispatches to an arbitrary subreducer.
   *
   * Concretely, it chains together all of the reducers, but in practice it is only used
   * when the reducers handle a disjoint set of action types.
   */
  private class ReduceReducers extends DataFlow::CallNode, DelegatingReducer {
    ReduceReducers() {
      this = API::moduleImport("reduce-reducers").getACall() or
      this = reduxActionsLike().getMember("reduceReducers").getACall()
    }

    override DataFlow::Node getAPlainHandlerArg() {
      result = getAnArgument()
      or
      result = getArgument(0).getALocalSource().(DataFlow::ArrayCreationNode).getAnElement()
    }
  }

  private class CreateReducer extends API::CallNode, DelegatingReducer {
    CreateReducer() {
      this = API::moduleImport("@reduxjs/toolkit").getMember("createReducer").getACall()
    }

    private API::Node getABuilderRef() {
      result = getParameter(1).getParameter(0)
      or
      result = getABuilderRef().getAMember().getReturn()
    }

    override DataFlow::Node getTypeTagHandlerArg(string propValue) {
      exists(API::CallNode addCase |
        addCase = getABuilderRef().getMember("addCase").getACall() and
        result = addCase.getArgument(1) and
        propValue = getATypeTagFromNode(addCase.getArgument(0))
      )
    }
  }

  /**
   * A source of the `dispatch` function, used as starting point for `getADispatchFunctionReference`.
   */
  abstract private class DispatchFunctionSource extends DataFlow::SourceNode { }

  /**
   * A value that is dispatched, that is, flows to the first argument of `dispatch`
   * (but where the call to `dispatch` is not necessarily explicit in the code).
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

  /** Gets the `action` parameter of a reducer that isn't behind an implied type guard. */
  DataFlow::SourceNode getAnUntypedActionInReducer() {
    exists(ReducerArg reducer |
      not reducer.isTypeTagHandler(_) and
      result = reducer.getASource().(DataFlow::FunctionNode).getParameter(1)
    )
  }

  /**
   * A function value, which, for some string `T` behaves as the function `x => {type: T, payload: x}`.
   */
  class ActionCreator extends DataFlow::SourceNode {
    ActionCreator::Range range;
  
    ActionCreator() { this = range }

    string getTypeTag() { result = range.getTypeTag() }

    DataFlow::FunctionNode getMiddlewareFunction() { result = range.getMiddlewareFunction() }

    /** Gets a data flow node referring to this action creator. */
    private DataFlow::SourceNode ref(DataFlow::TypeTracker t) {
      t.start() and
      result = this 
      or
      exists(API::CallNode bind, string prop |
        bind = API::moduleImport(["redux", "@reduxjs/toolkit"]).getMember("bindActionCreators").getACall() and
        ref(t.continue()).flowsTo(bind.getParameter(0).getMember(prop).getARhs()) and
        result = bind.getReturn().getMember(prop).getAnImmediateUse()
      ) // TODO: step through mapDispatchToProps etc
      or
      exists(DataFlow::TypeTracker t2 |
        result = ref(t2).track(t2, t)
      )
    }
    
    /** Gets a data flow node referring to this action creator. */
    DataFlow::SourceNode ref() {
      result = ref(DataFlow::TypeTracker::end())
    }
  
    /**
     * Gets a node that evaluates to `outcome` if `action` is an action created by this action creator.
     */
    DataFlow::Node getATypeTest(DataFlow::Node action, boolean outcome) {
      // TODO: handle switch (maybe via MembershipCandidate)
      exists(DataFlow::CallNode call |
        call = ref().getAMethodCall("match") and
        action = call.getArgument(0) and
        outcome = true and
        result = call
      )
      or
      exists(DataFlow::SourceNode actionSrc, EqualityTest test |
        actionSrc = getAnUntypedActionInReducer() and
        actionSrc.flowsTo(action) and
        test.hasOperands(actionSrc.getAPropertyRead("type").asExpr(), any(Expr e | e.mayHaveStringValue(getTypeTag()))) and
        outcome = test.getPolarity() and
        result = test.flow()
      )
      // TODO: manual tests here
    }

    /** Gets a data flow node referring a payload of this action (usually in the reducer function). */
    DataFlow::SourceNode getAPayloadReference() {
      // `if (x.match(action)) { ... action.payload ... }`
      exists(DataFlow::Node test, boolean outcome, DataFlow::Node action, ConditionGuardNode guard |
        // Used in: Grafana
        test = getATypeTest(action, outcome) and
        result = action.getALocalSource().getAPropertyRead("payload") and
        guard.getTest() = test.asExpr() and
        guard.getOutcome() = outcome and
        guard.dominates(result.getBasicBlock())
      )
      or
      exists(ReducerArg reducer |
        reducer.isTypeTagHandler(getTypeTag()) and
        result = reducer.getASource().(DataFlow::FunctionNode).getParameter(1).getAPropertyRead("payload")
      )
    }
  }

  module ActionCreator {
    abstract class Range extends DataFlow::SourceNode {
      abstract string getTypeTag();
      DataFlow::FunctionNode getMiddlewareFunction() { none() }
      DataFlow::Node getAnAdditionalTypeTest(DataFlow::Node action, boolean outcome) { none() }
    }

    class SingleAction extends Range, API::CallNode {
      SingleAction() {
        this =
          API::moduleImport(["@reduxjs/toolkit", "redux-actions", "redux-ts-utils"])
              .getMember("createAction")
              .getACall()
      }

      override string getTypeTag() {
        getArgument(0).mayHaveStringValue(result)
      }
    }

    /** One of the dispatchers created by a call to `createActions` from `redux-actions`. */
    class MultiAction extends Range {
      API::CallNode createActions;
      string name;

      MultiAction() {
        createActions = API::moduleImport("redux-actions").getMember("createActions").getACall() and
        this = createActions.getReturn().getMember(name).getAnImmediateUse()
      }

      override DataFlow::FunctionNode getMiddlewareFunction() {
        result.flowsTo(createActions.getParameter(0).getMember(getTypeTag()).getARhs())
      }

      override string getTypeTag() {
        result = name.regexpReplaceAll("([a-z])([A-Z])", "$1_$2").toUpperCase()
      }
    }
  }

  /**
   * Step from a typed action creation to its use (usually in a reducer function).
   */
  // predicate actionToReducerStep(DataFlow::Node input, DataFlow::SourceNode output) {
  //   exists(ActionCreator action |
  //     exists(DataFlow::CallNode call | call = action.getADispatchInvocation() |
  //       exists(int i |
  //         input = call.getArgument(i) and
  //         output = action.getMiddlewareFunction().getParameter(i)
  //       )
  //       or
  //       not exists(action.getMiddlewareFunction()) and
  //       input = call.getArgument(0) and
  //       output = action.getAPayloadReference()
  //     )
  //     or
  //     input = action.getMiddlewareFunction().getReturnNode() and
  //     output = action.getAPayloadReference()
  //   )
  // }

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
        this = API::moduleImport(["reselect", "@reduxjs/toolkit"]).getMember("createSelector").getACall()
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

  module Debbugging {
    predicate missedDispatch(DataFlow::SourceNode node) {
      // Many originally missed in grafana due to thunks in mapDispatchToProps functions, but found now
      // Still missing navigateToExplore due to: possibly unresolved import?
      node.asExpr().(Identifier).getName() = "dispatch" and
      not node = getADispatchFunctionReference()
    }

    predicate missedReducerUse(DataFlow::SourceNode node) {
      node.flowsToExpr(any(Identifier id | id.getName().regexpMatch("(?i).*reducer"))) and
      not node = any(ReducerArg arg).getASource()
    }

    predicate missedReducerFunction(DataFlow::FunctionNode function) {
      function.getParameter(0).getName() = "state" and
      (
        function.getParameter(1).getName() = "action"
        or
        exists(function.getParameter(1).getAPropertyRead("payload"))
      ) and
      not function = any(ReducerArg arg).getASource()
    }

    predicate missedPayloadSource(DataFlow::PropRead payload) {
      payload.getPropertyName() = "payload" and
      not payload = any(ActionCreator c).getAPayloadReference()
    }

    predicate unconnectedReducer(DelegatingReducer r) {
      // Findings:
      //   'workspaceReducer' in graphql-playground: manually invoked with state.getIn(['workspace', blah])
      //   combineReducers in Signal-Destop, not sure why
      not exists(r.getUseSite())
    }

    predicate test(DataFlow::PropWrite write, string name) {
      name = write.getPropertyNameExpr().getStringValue()
    }
  }
}
