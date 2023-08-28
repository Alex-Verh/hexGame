package server;

/**
 * The PlayerChatLacking class is the exception that is thrown
 *      when a user does not have whisper enabled.
 */
public class PlayerChatLacking extends Exception {
    /**
     * Creates a new PlayerChatLacking.
     * @param username the username of the user
     */
    //@requires !username.isEmpty() && username.length() <= 20;
    //@pure;
    public PlayerChatLacking(String username) {
        super("Player " + username + " does not have chat extension");
    }
}
