/**
 * @name Client-side cross-site scripting
 * @description Writing user input directly to the DOM allows for
 *              a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @id js/xss
 * @tags security
 *       external/cwe/cwe-079
 *       external/cwe/cwe-116
 */

import javascript
import semmle.javascript.security.dataflow.DomBasedXss::DomBasedXss
import DataFlow::PathGraph

from DataFlow::Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
  (
    cfg instanceof HtmlInjectionConfiguration or
    cfg instanceof JQueryHtmlOrSelectorInjectionConfiguration
  ) and
  cfg.hasFlowPath(source, sink) and
  not sink.getNode() = any(ExprStmt stmt).getExpr().flow() and
  not sink.getNode() = any(MethodCallExpr m).getCallee().flow()
select sink.getNode(), source, sink, " vulnerability due to $@.", source.getNode(),
  "user-provided value"
