package server;

/**
 * The PlayerOfflineException class is the exception that is thrown when a user is not online.
 */
public class PlayerOfflineException extends Exception {

    /**
     * Creates a new PlayerOfflineException.
     * @param username the username of the user
     */
    //@requires !username.isEmpty() && username.length() <= 20;
    //@pure;
    public PlayerOfflineException(String username) {
        super("Player " + username + " is not online");
    }
}
