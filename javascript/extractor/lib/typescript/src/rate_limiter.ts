
type Thunk = () => void;

const maxConcurrentRequests = 50;

/**
 * Returns a function with the same signature as `getPromise`, but which only allows `maxConcurrentRequests`
 * concurrent executions of the underlying function.
 */
export function rateLimit<A extends any[], T>(getPromise: (...args: A) => Promise<T>): typeof getPromise {
    let queue: Thunk[] = [];
    let currentRunning = 0;

    function onFinished() {
        --currentRunning;
        if (queue.length > 0) {
            queue.pop()();
        }
    }

    function execute(args: A) {
        ++currentRunning;
        // Note: Avoid using .finally() as it was only introduced in Node 10.0.0.
        return getPromise(...args).then(v => {
            onFinished();
            return v;
        }, err => {
            onFinished();
            return Promise.reject(err)
        });
    }

    return function(...args: A) {
        if (currentRunning < maxConcurrentRequests) {
            return execute(args);
        } else {
            return new Promise(function(resolve, reject) {
                queue.push(function() {
                    execute(args).then(resolve, reject);
                });
            });
        }
    };
}
