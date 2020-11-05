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
  //
  // DISPATCH TO REDUCER
  //

  /**
   * A value which, when invoked as a function, creates an action instance to be dispatched.
   *
   * The Redux model establishes flow between calls to an action builder and the corresponding
   * action payload in the reducer function.
   */
  class ActionBuilder extends DataFlow::SourceNode {
    ActionBuilder::Range range;

    ActionBuilder() { this = range }

    /**
     * Gets a function which acts as a "middleware" for this action, transforming the arguments to
     * the action builder before reaching the reducer.
     */
    DataFlow::FunctionNode getActionMiddlewareFunction() { result = range.getActionMiddlewareFunction() }

    /** Gets a data flow node referring to this action builder. */
    private DataFlow::SourceNode ref(DataFlow::TypeTracker t) {
      t.start() and
      result = this
      or
      exists(DataFlow::TypeTracker t2 |
        result = ref(t2).track(t2, t)
      )
    }
    
    /** Gets a data flow node referring to this action builder. */
    DataFlow::SourceNode ref() {
      result = ref(DataFlow::TypeTracker::end())
    }

    final DataFlow::CallNode getAnActionInvocation() {
      result = ref().getACall() // use API graphs
      or
      result = getAnAdditionalInvocation()
    }

    DataFlow::CallNode getAnAdditionalInvocation() { none() }

    string getTypeTag() { result = range.getTypeTag() }

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
      result = API::moduleImport("redux-actions").getMember("handleActions").getParameter(0).getMember(getTypeTag()).getParameter(1).getAUse()
    }
  }

  module ActionBuilder {
    abstract class Range extends DataFlow::SourceNode {
      DataFlow::FunctionNode getActionMiddlewareFunction() { none() }
      string getTypeTag() { none() }
    }

    class SingleActionBuilder extends Range, DataFlow::CallNode {
      SingleActionBuilder() {
        this = API::moduleImport(["@reduxjs/toolkit", "redux-actions"]).getMember("createAction").getACall()
      }

      override string getTypeTag() {
        getArgument(0).mayHaveStringValue(result)
      }
    }

    class BulkActionBuilder extends Range {
      DataFlow::CallNode createActions;
      string name;

      BulkActionBuilder() {
        createActions = API::moduleImport("redux-actions").getMember("createActions").getACall() and 
        this = createActions.getAPropertyRead(name)
      }

      override DataFlow::FunctionNode getActionMiddlewareFunction() {
        result.flowsTo(createActions.getOptionArgument(0, getTypeTag()))
      }

      override string getTypeTag() {
        result = name.regexpReplaceAll("([a-z])([A-Z])", "$1_$2").toUpperCase()
      }
    }
  }

  predicate dispatchStep(DataFlow::Node input, DataFlow::SourceNode output) {
    exists(ActionBuilder action |
      exists(DataFlow::CallNode call | call = action.getAnActionInvocation() |
        exists(int i |
          input = call.getArgument(i) and
          output = action.getActionMiddlewareFunction().getParameter(i)
        )
        or
        not exists(action.getActionMiddlewareFunction()) and
        input = call.getArgument(0) and
        output = action.getAPayloadReference()
      )
      or
      input = action.getActionMiddlewareFunction().getReturnNode() and
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
  abstract class RootStateNode extends API::Node {
  }

  /**
   * Holds if the return-value of `reducer` should flow to `state`.
   */
  predicate reduxReducerState(API::Node reducer, API::Node state) {
    // Note: There is a deliberate cartesian product in the base case here.
    // In practice there are very few root reducers (1 for the real entry point, plus a few in tests).
    (
      reducer = API::moduleImport(["redux", "redux-immutable"]).getMember("combineReducers").getParameter(0)
      or
      reducer = API::moduleImport("redux-actions").getMember("handleActions").getParameter(0).getAMember()
    ) and
    state instanceof RootStateNode
    or
    exists(API::Node prevReducer, API::Node prevState, string prop |
      reduxReducerState(prevReducer, prevState) and
      reducer = prevReducer.getMember(prop) and
      state = prevState.getMember(prop)
    )
  }

  predicate reducerStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(API::Node reducer, API::Node state |
      reduxReducerState(reducer, state) and
      pred = reducer.getReturn().getARhs() and
      succ = state.getAUse()
    )
  }

  private class ReducerStep extends DataFlow::AdditionalFlowStep {
    ReducerStep() {
      reducerStep(this, _)
    }

    override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
      reducerStep(this, succ) and pred = this
    }
  }



  // React-redux model
  private module ReactRedux {
    API::Node connect() { result = API::moduleImport("react-redux").getMember("connect") }

    /** The first argument to a `mapStateToProps` function, seen as a redux state. */
    private class ReactConnectState extends RootStateNode {
      ReactConnectState() {
        this = connect().getParameter(0).getParameter(0)
      }
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
      DataFlow::FunctionNode getMapStateToPropsFunction() {
        result = getCallback(0)
      }

      /**
       * Gets the second argument to `connect`, usually known as `mapDispatchToProps`.
       */
      DataFlow::Node getMapDispatchToPropsNode() {
        result = getArgument(1)
      }

      /**
       * Gets the second argument to `connect`, usually known as `mapDispatchToProps`.
       */
      DataFlow::FunctionNode getMapDispatchToPropsFunction() {
        result = getCallback(1)
      }

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
        result.getAComponentCreatorReference().flowsTo(getAComponentTransformer().getACall().getArgument(0))
      }
    }

    private class ConnectionStep extends DataFlow::AdditionalFlowStep, ConnectCall {
      override predicate step(DataFlow::Node pred, DataFlow::Node succ) {
        pred = getMapStateToPropsFunction().getReturnNode() and
        succ = getReactComponent().getADirectPropsAccess()
        or
        // Boost property depth tracking
        exists(string name |
          pred = getMapStateToPropsFunction().getReturnNode().getALocalSource().getAPropertySource(name) and
          succ = getReactComponent().getAPropRead(name)
        )
      }
    }

    /**
     * Treats call to `this.props.foo(x)` as a dispatch of the `foo` action, if the `foo` action
     * was passed in through `mapDispatchToProps`:
     */
    private class ReduxToolkitDispatch extends ActionBuilder {
      override DataFlow::CallNode getAnAdditionalInvocation() {
        exists(ConnectCall call, string name |
          ref().flowsTo(call.getDispatchPropNode(name)) and
          result = call.getReactComponent().getAPropRead(name).getACall()
        )
      }
    }
  }


  module Reselect {
    class ReselectStateNode extends RootStateNode {
      ReselectStateNode() {
        this = API::moduleImport("reselect").getMember("createSelector").getParameter(0).getAMember().getParameter(0)
      }
    }
  }
}
