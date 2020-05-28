package com.semmle.js.nodeinterop;

import com.semmle.util.exception.ResourceError;

/**
 * Exception thrown by {@link FireAndForgetProcess} when the process exited
 * with a non-zero exit code.
 */
public class ProcessFailedError extends ResourceError {
  private static final long serialVersionUID = -615842825915841442L;

  public ProcessFailedError(String message, Throwable throwable) {
    super(message,throwable);
  }

  public ProcessFailedError(String message) {
    super(message);
  }
}
