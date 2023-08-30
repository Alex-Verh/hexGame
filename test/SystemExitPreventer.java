import java.security.Permission;

/**
 * Provides a mechanism to prevent calls to {@code System.exit()} by replacing the current
 * {@code SecurityManager} with a custom implementation that throws an {@code ExitError}
 * instead of actually terminating the JVM.
 *
 * <p>This class is typically used in testing scenarios where the behavior of {@code System.exit()}
 * needs to be captured and asserted without shutting down the test runner.</p>
 */
public class SystemExitPreventer {

    /**
     * Replaces the current {@code SecurityManager} with the {@code NoExitSecurityManager}.
     * After calling this method, any subsequent calls to {@code System.exit()} will result
     * in an {@code ExitError} being thrown instead of the JVM terminating.
     */
    public static void preventSystemExit() {
        System.setSecurityManager(new NoExitSecurityManager());
    }

    /**
     * Custom {@code SecurityManager} implementation that throws an {@code ExitError} when
     * {@code System.exit()} is called, preventing the JVM from actually terminating.
     */
    public static class NoExitSecurityManager extends SecurityManager {

        @Override
        public void checkExit(int status) {
            super.checkExit(status);
            throw new ExitError(status);
        }

        @Override
        public void checkPermission(Permission perm) {
            // Allow anything.
        }

        @Override
        public void checkPermission(Permission perm, Object context) {
            // Allow anything.
        }
    }
}
