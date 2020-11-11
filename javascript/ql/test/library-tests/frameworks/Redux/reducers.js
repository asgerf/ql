import { combineReducers, createStore } from 'redux';
import { createSelector } from 'reselect';
import importedReducer from './exportedReducer';
import { nestedReducer } from './exportedReducer';

let reducer = combineReducers({
    foo: {
        bar: {
            baz: (state, action) => state
        },
        baloon: importedReducer,
    },
    nestedReducer
});
let store = createStore(reducer);

let fooBarBazSelector = createSelector(state => state.foo.bar.baz);
let baloonSelector = createSelector(state => state.foo.baloon);
let nestedSelector = createSelector(state => state.nestedReducer);
