package client.controller;
import java.io.*;
import java.net.Socket;

/**
 * Sends the messages to the server.
 */
public class Protocol {

    public final BufferedWriter writer;
    //@public invariant writer != null;

    /**
     * Creates a new sender.
     * @param socket the socket to sends messages to
     * @throws IOException if an I/O error occurs when creating the input stream.
     */
    //@requires socket != null;
    public Protocol(Socket socket) throws IOException {
        writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
    }


    /**
     * Sends a hello message to connect to server.
     * @return true || false if message was sent or not
     */
    //@ensures \result == true || \result == false;
    //@pure;
    public boolean sendHello() {
        try {
            writer.write("HELLO~" + "AlexClient" + "~RANK~CHAT" + "\n");
            writer.flush();
            return true;
        } catch (IOException e) {
            return false;
        }

    }

    /**
     * Sends message about login with username.
     * @param username the username of the player
     * @return true || false if message was sent or not
     */
    //@requires !username.isEmpty() && username.length() <= 20;
    //@ensures \result == true || \result == false;
    //@pure;
    public boolean sendUsername(String username) {
        try {
            writer.write("LOGIN~" + username + "\n");
            writer.flush();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    /**
     * Sends move message at specified index.
     * @param index the index of the move
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@requires index >= 0 && index < 81;
    //@pure;
    public void sendMove(int index) throws IOException {
        writer.write("MOVE~" + index + "\n");
        writer.flush();
    }

    /**
     * Sends chat message to server.
     * @param message the message to be sent
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@requires !message.isEmpty();
    //@pure;
    public void sendMessage(String message) throws IOException {
        String finalMessage = escape(message);
        System.out.println("You told everyone: " + finalMessage);
        writer.write("CHAT~" + finalMessage + "\n");
        writer.flush();
    }

    /**
     * Sends RANK command to server.
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@pure;
    public void sendRank() throws IOException {
        writer.write("RANK" + "\n");
        writer.flush();
    }

    /**
     * Sends QUIT command to server.
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@pure;
    public void sendQueue() throws IOException {
        writer.write("QUEUE" + "\n");
        writer.flush();
    }

    /**
     * Sends LIST command to server.
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@pure;
    public void sendList() throws IOException {
        writer.write("LIST" + "\n");
        writer.flush();
    }

    /**
     * Sends message to a user.
         * @param username the username of the user
     * @param message the message to be sent
     * @throws IOException if an I/O error occurs when sending the message
     */
    //@requires !username.isEmpty() && !message.isEmpty() && username.length() <= 20;
    //@pure;
    public void sendWhisper(String username, String message) throws IOException {
        String finalMessage = escape(message);
        System.out.println("You told " + username + " : " + finalMessage);
        writer.write("WHISPER~" + username + "~" + finalMessage + "\n");
        writer.flush();
    }

    /**
     * Apply escape characters for special characters
     * @param str string
     * @return formatted string
     */
    //@requires !str.isEmpty();
    private String escape(String str) {
        return str.replace("\\", "\\\\").replace("~", "\\~");
    }
}
