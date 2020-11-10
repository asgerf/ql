/**
 * Provides classes and predicates for reasoning about data flow through the redux package.
 */

import javascript

// The core Redux model contributes two kinds of steps:
//   1. From dispatch argument to reducer parameter ("dispatch step")
//   2. From reducer return-value to state access ("reducer step")
//
// A third kind of step is often needed to adapter libraries like `react-redux`, for example:
//   3. From mapStateToProps return-value to props access in react component
//
// The third kind of step is technically independent of the core Redux library, but
// this file includes modeling of such adapter libraries as well.
module Redux {
  private class ReduxRootStateTag extends DataFlow::CustomNodes::SingletonNodeTag {
    ReduxRootStateTag() { this = "redux-root-state" }
  }

  private class ReduxRootStateNode extends DataFlow::CustomNodes::SingletonNode,
    DataFlow::SourceNode::Range {
    override ReduxRootStateTag tag;
  }

  private ReduxRootStateNode rootState() { any() }

  //
  // DISPATCH TO REDUCER
  //
  /**
   * A value which, when invoked as a function, creates and/or dispatches an action to the Redux store.
   *
   * The Redux model establishes data flow between calls to a dispatcher and the corresponding
   * action payload in the reducer function.
   */
  class Dispatcher extends DataFlow::SourceNode {
    Dispatcher::Range range;

    Dispatcher() { this = range }

    /**
     * Gets a function which acts as a "middleware" for this dispatcher, transforming its arguments
     * into the actual action that gets dispatched.
     *
     * If no middleware exists, the first argument to the dispatcher is treated as the action itself.
     */
    DataFlow::FunctionNode getMiddlewareFunction() { result = range.getMiddlewareFunction() }

    /** Gets a data flow node referring to this dispatcher. */
    private DataFlow::SourceNode ref(DataFlow::TypeTracker t) {
      t.start() and
      result = this
      or
      exists(DataFlow::TypeTracker t2 | result = ref(t2).track(t2, t))
    }

    /** Gets a data flow node referring to this dispatcher. */
    DataFlow::SourceNode ref() { result = ref(DataFlow::TypeTracker::end()) }

    /** Gets a call to the dispatcher. */
    final DataFlow::CallNode getADispatchInvocation() {
      result = ref().getACall()
      or
      result = getAnAdditionalDispatchInvocation()
    }

    /**
     * Gets an additional call to the dispatcher, contributed by a subclass.
     *
     * This is a hook for modeling "framework bridges" like `react-redux`, where steps specific to one
     * UI framework can affect the flow of Redux dispatchers.
     */
    DataFlow::CallNode getAnAdditionalDispatchInvocation() { none() }

    /**
     * Gets the value of `propName` on the dispatched action object, which acts as a "type tag" for this action,
     * distinguishing it from other types of actions.
     *
     * For example, for a call `dispatch({type: "foo", data})` we would have `getTypeTag("type") = "foo"`.
     *
     * Typically `propName` is `"type"`.
     */
    string getTypeTag(string propName) { result = range.getTypeTag(propName) }

    /** Gets a data flow node referring a payload of this action (usually in the reducer function). */
    DataFlow::SourceNode getAPayloadReference() {
      exists(DataFlow::CallNode match, ConditionGuardNode guard |
        match = ref().getAMethodCall("match") and
        result = match.getArgument(0).getALocalSource().getAPropertyRead("payload") and
        guard.getTest() = match.asExpr() and
        guard.getOutcome() = true and
        guard.dominates(result.getBasicBlock())
      )
      or
      result =
        API::moduleImport("redux-actions")
            .getMember("handleActions")
            .getParameter(0)
            .getMember(getTypeTag("type"))
            .getParameter(1)
            .getAUse()
    }
  }

  module Dispatcher {
    abstract class Range extends DataFlow::SourceNode {
      DataFlow::FunctionNode getMiddlewareFunction() { none() }

      string getTypeTag(string propName) { none() }
    }

    /** A dispatcher created by `createAction` from either `@reduxjs/toolkit` or `redux-actions`. */
    class SingleAction extends Range, DataFlow::CallNode {
      SingleAction() {
        this =
          API::moduleImport(["@reduxjs/toolkit", "redux-actions"])
              .getMember("createAction")
              .getACall()
      }

      override string getTypeTag(string propName) {
        propName = "type" and
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
        // TODO: this could be an API node and then we connect getParameter()/getReturn() for each API node
        result.flowsTo(createActions.getParameter(0).getMember(getTypeTag("type")).getARhs())
      }

      override string getTypeTag(string propName) {
        propName = "type" and
        result = name.regexpReplaceAll("([a-z])([A-Z])", "$1_$2").toUpperCase()
      }
    }
  }

  predicate dispatchStep(DataFlow::Node input, DataFlow::SourceNode output) {
    exists(Dispatcher action |
      exists(DataFlow::CallNode call | call = action.getADispatchInvocation() |
        exists(int i |
          input = call.getArgument(i) and
          output = action.getMiddlewareFunction().getParameter(i)
        )
        or
        not exists(action.getMiddlewareFunction()) and
        input = call.getArgument(0) and
        output = action.getAPayloadReference()
      )
      or
      input = action.getMiddlewareFunction().getReturnNode() and
      output = action.getAPayloadReference()
    )
  }

  // TODO: generalize to handle plain redux style
  private class DispatchStep extends DataFlow::AdditionalFlowStep {
    DispatchStep() { dispatchStep(this, _) }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      dispatchStep(pred, succ) and pred = this
    }
  }

  //
  // REDUCER TO STATE ACCESS
  //
  /**
   * EXPERIMENTAL. This API is public may have breaking changes in the future.
   *
   * An API node corresponding to a reference to the root state object in a Redux app.
   */
  abstract class RootStateNode extends API::Node { }

  API::Node rootReducer() {
    result = API::moduleImport("redux").getMember("createStore").getParameter(0)
    or
    result =
      API::moduleImport("@reduxjs/toolkit")
          .getMember("configureStore")
          .getParameter(0)
          .getMember("reducer")
  }

  /** Gets a data flow node that flows to the root reducer. */
  private DataFlow::SourceNode nodeLeadingToRootReducer(DataFlow::TypeBackTracker t) {
    t.start() and
    result = rootReducer().getARhs().getALocalSource()
    or
    exists(DataFlow::Node mid | result.flowsTo(mid) |
      // Step through forwarding functions
      DataFlow::functionForwardingStep(mid, nodeLeadingToRootReducer(t.continue()))
      or
      // Step through function composition (usually composed with various state "enhancer" functions)
      exists(FunctionCompositionCall compose, DataFlow::CallNode call |
        call = compose.getACall() and
        nodeLeadingToRootReducer(t.continue()) = call and
        mid = [compose.getAnOperandNode(), call.getAnArgument()]
      )
    )
    or
    exists(DataFlow::TypeBackTracker t2 | result = nodeLeadingToRootReducer(t2).backtrack(t2, t))
  }

  /** Gets a data flow node that flows to the root reducer. */
  DataFlow::SourceNode nodeLeadingToRootReducer() {
    result = nodeLeadingToRootReducer(DataFlow::TypeBackTracker::end())
  }

  /**
   * Holds if `outerReducer` delegates handling of `state.prop` to `innerReducer`.
   *
   * Semantically it recognizes API calls to functions that essentially have this form:
   * ```js
   * function outerReducer(state, action) {
   *   return {
   *     prop: innerReducer(state.prop, action),
   *     ...
   *   }
   * }
   * 
   * // Code actually matched by this predicate (semantically equivalent to the above)
   * let outerReducer = combineReducers({
   *   prop: innerReducer
   * })
   * ```
   */
  predicate isStatePathReducer(API::Node outerReducer, API::Node innerReducer, string prop) {
    exists(API::CallNode call |
      call = API::moduleImport(["redux", "redux-immutable"]).getMember("combineReducers").getACall() and
      innerReducer = call.getParameter(0).getMember(prop) and
      outerReducer = call.getReturn()
    )
    or
    isStatePathReducer(_, outerReducer, _) and
    innerReducer = outerReducer.getMember(prop)
  }

  /**
   * Holds if actions dispatched to `outerReducer` are forwarded to `innerReducer`
   * when its property `propName` has value `propValue`.
   *
   * One can think of it as a function of the form:
   * ```js
   * function outerReducer(state, action) {
   *   if (action.propName === 'propValue') {
   *     return innerReducer(state, action);
   *   }
   *   ...
   * }
   *
   * // Code actually matched by this predicate (semantically equivalent to the above, with propName = "type")
   * let outerReducer = handleActions({
   *   propValue: innerReducer
   * })
   */
  predicate isTypeSwitchReducer(
    API::Node outerReducer, API::Node innerReducer, string propName, string propValue
  ) {
    exists(API::CallNode call |
      call = API::moduleImport("redux-actions").getMember("handleActions").getACall() and
      outerReducer = call.getReturn() and
      innerReducer = call.getParameter(0).getMember(propValue) and
      propName = "type"
    )
  }

  /**
   * Holds if the return value of `reducer` should flow to `state`.
   *
   * To avoid a full cartesian product between all root reducers and all root state accesses, this
   * predicate only includes reducers that operate on some access path within the state.
   *
   * For example, the callback in the `foo` property `.foo` access on the root state, and the
   * callback on the `baz` property corresponds to the `.bar.baz` access:
   * ```js
   * let reducer = combineReducers({
   *   foo: (state, payload) => { ... }
   *   bar: {
   *     baz: (state, payload) => { ... }
   *   }
   * })
   *
   * getRootState().foo // sees value from foo reducer
   * getRootState().bar.baz // sees value from bar.baz reducer
   * ```
   */
  predicate reducerAffectsStateAccessPath(API::Node reducer, API::Node state) {
    exists(API::Node outerReducer, string prop |
      isStatePathReducer(outerReducer, reducer, prop) and
      state = rootStateProp(prop) and
      nodeLeadingToRootReducer() = outerReducer.getAUse()
    )
    or
    exists(API::Node prevReducer |
      reducerAffectsStateAccessPath(prevReducer, state) and
      isTypeSwitchReducer(sourceOf(prevReducer), reducer, _, _)
    )
    or
    exists(API::Node prevReducer, API::Node prevState, string prop |
      reducerAffectsStateAccessPath(prevReducer, prevState) and
      isStatePathReducer(sourceOf(prevReducer), reducer, prop) and
      state = prevState.getMember(prop)
    )
  }

  /** Gets an API node that flows to `node`. */
  private API::Node sourceOf(API::Node node) { node.refersTo(result) }

  /** Gets an API node corresponding to an access of `prop` on the root state. */
  pragma[noinline]
  private API::Node rootStateProp(string prop) { result = any(RootStateNode n).getMember(prop) }

  /**
   * Holds if the step `pred -> succ` goes from the return value of a reducer to a state access.
   */
  predicate reducerStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(API::Node reducer, API::Node state |
      reducerAffectsStateAccessPath(reducer, state) and
      pred = reducer.getReturn().getARhs() and
      succ = state.getAUse()
    )
    or
    // For reducers that operate on the root state, we want to avoid a full cartesian product between
    // reducers and state accesses. To this end, we use the synthetic `redux-root-state` node as a junction,
    // so all reducers have a step to the root state, and the root state has a step to all its uses.
    exists(API::Node reducer |
      pred = nodeLeadingToRootReducer().(DataFlow::FunctionNode).getReturnNode() and
      succ = rootState()
    )
    or
    pred = rootState() and
    succ = any(RootStateNode n).getAUse()
  }

  private class ReducerStep extends DataFlow::AdditionalFlowStep {
    ReducerStep() { reducerStep(this, _) }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      reducerStep(this, succ) and pred = this
    }
  }

  // React-redux model
  private module ReactRedux {
    API::Node connect() { result = API::moduleImport("react-redux").getMember("connect") }

    /** The first argument to a `mapStateToProps` function, seen as a redux state. */
    private class ReactConnectState extends RootStateNode {
      ReactConnectState() { this = connect().getParameter(0).getParameter(0) }
    }

    /**
     * A call to `connect()`, typically as part of a code pattern like the following:
     * ```js
     * let withConnect = connect(mapStateToProps, mapDispatchToProps);
     * let MyAwesomeComponent = compose(withConnect, otherStuff)(MyComponent);
     * ```
     */
    private class ConnectCall extends DataFlow::CallNode {
      ConnectCall() { this = connect().getACall() }

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
       * Gets the function flowing to the first argument to `connect`, usually known as `mapStateToProps`.
       */
      DataFlow::FunctionNode getMapStateToPropsFunction() { result = getCallback(0) }

      /**
       * Gets the second argument to `connect`, usually known as `mapDispatchToProps`.
       */
      DataFlow::Node getMapDispatchToPropsNode() { result = getArgument(1) }

      /**
       * Gets the second argument to `connect`, usually known as `mapDispatchToProps`.
       */
      DataFlow::FunctionNode getMapDispatchToPropsFunction() { result = getCallback(1) }

      /**
       * Gets a data-flow node that should flow to `props.name` via the `mapDispatchToProps` function.
       */
      DataFlow::Node getDispatchPropNode(string name) {
        result = getMapDispatchToPropsNode().getALocalSource().getAPropertyWrite(name).getRhs()
        or
        exists(DataFlow::CallNode bind |
          bind = API::moduleImport("redux").getMember("bindActionCreators").getACall() and
          bind.flowsTo(getMapDispatchToPropsFunction().getReturnNode()) and
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

    private class ConnectionStep extends DataFlow::AdditionalFlowStep, ConnectCall {
      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        pred = getMapStateToPropsFunction().getReturnNode() and
        succ = getReactComponent().getADirectPropsAccess()
        or
        // Boost property depth tracking
        exists(string name |
          pred =
            getMapStateToPropsFunction().getReturnNode().getALocalSource().getAPropertySource(name) and
          succ = getReactComponent().getAPropRead(name)
        )
      }
    }

    /**
     * Treats call to `this.props.foo(x)` as a dispatch of the `foo` action, if the `foo` action
     * was passed in through `mapDispatchToProps`:
     */
    private class ReduxToolkitDispatch extends Dispatcher {
      override DataFlow::CallNode getAnAdditionalDispatchInvocation() {
        exists(ConnectCall call, string name |
          ref().flowsTo(call.getDispatchPropNode(name)) and
          result = call.getReactComponent().getAPropRead(name).getACall()
        )
      }
    }
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
      SelectorStateArg() {
        this = any(CreateSelectorCall c).getSelectorFunction(_).getParameter(0)
      }
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
      SelectorStep() {
        selectorStep(_, this)
      }

      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        selectorStep(pred, succ) and
        this = succ
      }
    }
  }
}
