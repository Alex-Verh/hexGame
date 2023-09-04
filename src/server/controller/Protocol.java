package server.controller;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Sends the messages to the writer.
 */
public class Protocol {
    /**
     * Private utility method to send a message to the provided writer.
     * The method ensures that the message is written and flushed.
     * @param writer the BufferedWriter to which the message needs to be sent
     * @param message the actual message string
     * @throws IOException if there's an error writing the message
     */
    //@ requires writer != null && message != null;
    //@pure;
    private static void sendMessage(BufferedWriter writer, String message) throws IOException {
        writer.write(message + "\n");
        writer.flush();
    }

    /**
     * Sends a hello message.
     *
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void hello(BufferedWriter writer) throws IOException {
        sendMessage(writer, "HELLO~AlexServer~CHAT~RANK");
    }

    /**
     * Sends a login message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void loggedIn(BufferedWriter writer) throws IOException {
        sendMessage(writer, "LOGIN");
    }

    /**
     * Sends a move message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendMove(BufferedWriter writer, int move) throws IOException {
        sendMessage(writer, "MOVE~" + move);
    }

    /**
     * Sends a new game message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendNewGame(BufferedWriter writer, String user1, String user2) throws IOException {
        sendMessage(writer, "NEWGAME~" + user1 + "~" + user2);
    }

    /**
     * Sends a victory message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void victory(BufferedWriter writer, String winner) throws IOException {
        sendMessage(writer, "GAMEOVER~VICTORY~" + winner);
    }

    /**
     * Sends a disconnect message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void disconnect(BufferedWriter writer, String user) throws IOException {
        sendMessage(writer, "GAMEOVER~DISCONNECT~" + user);
    }

    /**
     * Sends a gameover message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void gameover(BufferedWriter writer) throws IOException {
        sendMessage(writer, "GAMEOVER");
    }

    /**
     * Sends a error message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void error(BufferedWriter writer, String error) throws IOException {
        sendMessage(writer, "ERROR~" + error);
    }

    /**
     * Sends a chat message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendChat(BufferedWriter writer, String user, String message) throws IOException {
        sendMessage(writer, "CHAT~" + user + "~" + message);
    }

    /**
     * Sends a whisper message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendWhisper(BufferedWriter writer, String user, String message) throws IOException {
        sendMessage(writer, "WHISPER~" + user + "~" + message);
    }

    /**
     * Sends a cannot whisper message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendCannotWhisper(BufferedWriter writer, String recipient) throws IOException {
        sendMessage(writer, "CANNOTWHISPER~" + recipient);
    }

    /**
     * Sends a list message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendList(BufferedWriter writer, List<String> users) throws IOException {
        sendMessage(writer, "LIST~" + String.join("~", users));
    }

    /**
     * Sends a rank message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendRank(BufferedWriter writer, Map<String, Integer> ranks) throws IOException {
        StringBuilder rankBuilder = new StringBuilder();
        List<Map.Entry<String, Integer>> rankList = new ArrayList<>(ranks.entrySet());
        rankList.sort((x, y) -> y.getValue().compareTo(x.getValue()));

        for (Map.Entry<String, Integer> entry : rankList) {
            rankBuilder.append(entry.getKey()).append("~").append(entry.getValue()).append("~");
        }

        if (rankBuilder.length() > 0) {
            rankBuilder.setLength(rankBuilder.length() - 1); // Remove trailing '~'
        } else {
            rankBuilder.append(" ~ ");
        }

        sendMessage(writer, "RANK~" + rankBuilder);
    }

    /**
     * Sends a already logged message.
     * @param writer BufferedWriter to send the message to.
     * @throws IOException if there's an error writing the message.
     */
    //@ requires writer != null;
    //@pure;
    public static void sendALREADYLOGGEDIN(BufferedWriter writer) throws IOException {
        sendMessage(writer, "ALREADYLOGGEDIN");
    }
}
