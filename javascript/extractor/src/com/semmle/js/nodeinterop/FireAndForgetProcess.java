package com.semmle.js.nodeinterop;

import java.io.ByteArrayOutputStream;
import java.util.List;

import com.semmle.util.exception.InterruptedError;
import com.semmle.util.exception.ResourceError;
import com.semmle.util.logging.LogbackUtils;
import com.semmle.util.process.AbstractProcessBuilder;
import com.semmle.util.process.Builder;

import ch.qos.logback.classic.Level;

/**
 * Helper for spawning a short-lived Node processes and returning the contents
 * of its stdout as a string.
 */
public class FireAndForgetProcess {
  private Builder builder;
  private ByteArrayOutputStream out = new ByteArrayOutputStream();
  private ByteArrayOutputStream err = new ByteArrayOutputStream();

  public FireAndForgetProcess(List<String> command) {
    builder = new Builder(command, out, err);
    builder.expectFailure();
  }

  /**
   * Returns the underlying process builder.
   *
   * Use this to modify the current working directory and environment.
   */
  public Builder getBuilder() {
    return builder;
  }

  /** Returns everything written to stdout, as a string. */
  public String getStdout() {
    return new String(out.toByteArray());
  }

  /** Returns everything written to stderr, as a string. */
  public String getStderr() {
    return new String(err.toByteArray());
  }

  /**
   * Executes the process and returns the value of stdout if it succeeded.
   *
   * @return the value of stdout
   * @throws ResourceError if the process could not be started
   * @throws ProcessFailedError if the exit code was non-zero
   * @throws InterruptedError if the process timed out (10s by default)
   */
  public String execute() throws ResourceError, ProcessFailedError, InterruptedError {
    LogbackUtils.getLogger(AbstractProcessBuilder.class).setLevel(Level.INFO);
    int exitCode = builder.execute(NodeInterop.getTimeout());
    if (exitCode != 0) {
      throw new ProcessFailedError(getStderr());
    }
    return getStdout();
  }
}
