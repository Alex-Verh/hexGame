package client.controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PipedWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * Listens to the server and writes the messages.
 */
public class Listener implements Runnable {
    private final Socket socket;
    //@private invariant socket != null;

    private final PipedWriter writer;
    //@private invariant writer != null;

    private volatile boolean terminated = false;
    //@private invariant terminated == false || terminated == true;

    /**
     * Creates a new listener.
     * @param socket the socket of the server
     * @param writer the piped writer
     */
    //@requires socket != null && writer != null;
    public Listener(Socket socket, PipedWriter writer) {
        if (socket == null || writer == null) {
            throw new IllegalArgumentException("Socket or writer cannot be null");
        }
        this.socket = socket;
        this.writer = writer;
    }

    /**
     * Listen to the server and write the messages to print them.
     */
    //@pure;
    @Override
    public void run() {
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(socket.getInputStream()))) {
            while (!terminated) {
                String data = reader.readLine();
                if (data != null) {
                    detectCommand(data);
                } else {
                    throw new IOException("Server has been closed.");
                }
            }
        } catch (IOException e) {
            System.out.println("No server connection.");
        }
    }

    /**
     * Detects commands in a string.
     * @param serverMessage the string to check
     * @throws IOException if the piped writer fails
     */
    //@requires !serverMessage.isEmpty();
    //@pure;
    private void detectCommand(String serverMessage) throws IOException {
        String[] split = serverMessage.split("~", 3);
        String command = split[0].toUpperCase();

        switch (command) {
            case "MOVE", "NEWGAME" -> writeToPipe(serverMessage);
            case "GAMEOVER" -> writeToPipe("GAMEOVER");
            case "LIST" -> System.out.println(printList(serverMessage));
            case "WHISPER" -> System.out.println(formatMessage(split, "tells you"));
            case "CHAT" -> System.out.println(formatMessage(split, "said"));
            case "RANK" -> System.out.println(printRank(serverMessage));
            case "ERROR" -> System.out.println("ERROR: " + split[1]);
            default -> System.out.println("UNKNOWN: " + serverMessage);
        }
    }

    /**
     * Write the message to PipeWriter
     * @param message to be written
     * @throws IOException
     */
    //@requires message != null;
    //@ensures writer != null;
    private void writeToPipe(String message) throws IOException {
        writer.write(message + "\n");
        writer.flush();
    }

    /**
     * Formatter for a message
     * @param split splits the message
     * @param verb points out the action
     * @return formatted message
     */
    //@requires split != null;
    //@requires verb != null;
    //@ensures \result != null && \result.startsWith(split[1]);
    private String formatMessage(String[] split, String verb) {
        String message = replaceSpecialChars(split[2]);
        return split[1] + " " + verb + ": " + message;
    }

    /**
     * Replaces special chars with one needed
     * @param input String
     * @return String with special chars
     */
    //@requires input != null;
    //@ensures \result != null && \result.equals(input.replace("\\\\", "\\").replace("\\~", "~"));
    private String replaceSpecialChars(String input) {
        return input.replace("\\\\", "\\").replace("\\~", "~");
    }

    /**
     * Prints the rank of all players.
     * @param serverMessage the ranking extracted from the server
     * @return the rank of all players
     */
    //@requires !serverMessage.isEmpty();
    //@pure;
    public static String printRank(String serverMessage) {
        String header = "Rank of all the players:\n";
        String[] ranks = serverMessage.split("~");
        List<String> rankList = new ArrayList<>();
        for (int i = 1; i < ranks.length; i += 2) {
            rankList.add(ranks[i] + ": " + ranks[i + 1]);
        }
        return header + String.join("\n", rankList);
    }

    /**
     * Prints the list of all players.
     * @param serverMessage the list of players extracted from the server
     * @return the list of players
     */
    //@requires !serverMessage.isEmpty();
    //@pure;
    public static String printList(String serverMessage) {
        String header = "List of all the players:\n";
        String[] players = serverMessage.split("~");
        List<String> playerList = new ArrayList<>();
        for (int i = 1; i < players.length; i++) {
            playerList.add(players[i]);
        }

        StringBuilder result = new StringBuilder(header);
        for (int i = 0; i < playerList.size(); i++) {
            result.append(playerList.get(i));
            if ((i + 1) % 5 == 0) {
                result.append("\n");
            } else if (i < playerList.size() - 1) { // Avoid appending comma for the last element
                result.append(", ");
            }
        }
        return result.toString();
    }

    /**
     * Shuts down the listener
     */
    //@ensures terminated == true;
    public void terminate() {
        terminated = true;
    }
}
