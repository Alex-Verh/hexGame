/**
 * Represents an error that occurs when the system attempts to exit.
 * This error can be thrown to capture the status code of a System.exit() call
 * without actually terminating the JVM.
 *
 * <p>Typically used in testing scenarios where the System.exit() behavior needs
 * to be captured and asserted without shutting down the test runner.</p>
 */
public class ExitError extends Error {

    private final int status;

    /**
     * Constructs an ExitError with the specified exit status.
     *
     * @param status the exit status.
     */
    public ExitError(int status) {
        this.status = status;
    }

    /**
     * Retrieves the exit status associated with this error.
     *
     * @return the exit status.
     */
    public int getStatus() {
        return status;
    }
}
