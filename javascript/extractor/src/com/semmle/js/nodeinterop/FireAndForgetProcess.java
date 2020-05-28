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
   * @throws ProcessFailedError if the exit code was non-zero (this is a subtype of ResourceError)
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

  /**
   * Executes the process and returns the value of stdout if it succeeded.
   *
   * @param command command to execute
   * @return the value of stdout
   * @throws ResourceError if the process could not be started
   * @throws ProcessFailedError if the exit code was non-zero (this is a subtype of ResourceError)
   * @throws InterruptedError if the process timed out (10s by default)
   */
  public static String execute(List<String> command) throws ResourceError, ProcessFailedError, InterruptedError {
    return new FireAndForgetProcess(command).execute();
  }

  /**
   * Executes the process and returns the value of stdout if it succeeded.
   * The command will be retried if it times out.
   *
   * @param a human-readable name for the process to use in error messages
   * @param command command to execute
   * @return the value of stdout
   * @throws ResourceError if the process could not be started
   * @throws ProcessFailedError if the exit code was non-zero (this is a subtype of ResourceError)
   * @throws InterruptedError if final attempt timed out (10s by default)
   */
  public static String executeWithRetry(String name, List<String> command) throws ResourceError, ProcessFailedError, InterruptedError {
    return NodeInterop.withRetries(() -> execute(command), name);
  }
}
