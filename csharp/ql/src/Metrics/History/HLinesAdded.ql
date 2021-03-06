/**
 * @name Added lines
 * @description Number of added lines, across the revision history in the database.
 * @kind treemap
 * @treemap.warnOn highValues
 * @metricType file
 * @metricAggregate avg sum max
 * @deprecated
 */
import csharp
import external.VCS

from File f, int n
where n = sum(Commit entry, int churn | churn = entry.getRecentAdditionsForFile(f) and not artificialChange(entry) | churn)
select f, n
order by n desc
