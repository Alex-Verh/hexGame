package server.controller;


import server.PlayerChatLacking;
import server.PlayerOfflineException;

import java.io.*;
import java.net.Socket;

/**
 * Manages communication with a client by listening to its commands and
 * sending the appropriate response.
 */
public class ClientHandler implements Runnable {

    private final Socket clientSocket;
    //@ private invariant clientSocket != null;

    private PipedWriter pWriter;
    //@ private invariant pWriter != null;

    private PipedReader pReader;
    //@ private invariant pReader != null;

    private BufferedReader socketIn;
    //@ private invariant socketIn != null;

    private BufferedWriter socketOut;
    //@ private invariant socketOut != null;

    private String clientName;
    //@ private invariant !clientName.isEmpty() && clientName.length() <= 20;

    private final Server mainServer;
    //@ private invariant mainServer != null;

    private boolean isChatEnabled;
    //@ private invariant isChatEnabled == false || isChatEnabled == true;

    private boolean isChallengeEnabled;
    //@ private invariant isChallengeEnabled == false || isChallengeEnabled == true;

    private boolean isNoiseEnabled;
    //@ private invariant isNoiseEnabled == false || isNoiseEnabled == true;

    private boolean isRankingEnabled;
    //@ private invariant isRankingEnabled == false || isRankingEnabled == true;

    /**
     * Initializes a new ClientCommManager.
     * @param socket the client's socket
     * @param server the main server
     */
    //@ requires socket != null && server != null;
    public ClientHandler(Socket socket, Server server) {
        this.mainServer = server;
        this.clientSocket = socket;
        setUpStreamResources();
    }

    /**
     * Sets up necessary streaming resources for communication.
     */
    private void setUpStreamResources() {
        try {
            pWriter = new PipedWriter();
            pReader = new PipedReader(pWriter);
            socketIn = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
            socketOut = new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream()));
        } catch (IOException e) {
            System.out.println("Error initializing stream resources.");
        }
    }

    /**
     * Closes the client socket.
     */
    //@ pure;
    public void terminateConnection() {
        mainServer.removeClient(this);
    }

    /**
     * Returns client socket.
     * @return clientSocket
     */
    //@ ensures \result != null;
    //@ pure;
    public Socket getClientSocket() {
        return clientSocket;
    }

    /**
     * Returns client name.
     * @return clientName
     */
    //@ ensures !\result.isEmpty() && \result.length() <= 20;
    //@ pure;
    public String getClientName() {
        return clientName;
    }

    /**
     * Returns piped reader.
     * @return pReader
     */
    //@ ensures \result != null;
    //@ pure;
    public PipedReader getPipedReader() {
        return pReader;
    }

    /**
     * Returns socket writer.
     * @return socketOut
     */
    //@ ensures \result != null;
    //@ pure;
    public BufferedWriter getSocketWriter() {
        return socketOut;
    }

    /**
     * Runs the client handler.
     */
    @Override
    public void run() {
        processClientCommands();
    }

    /**
     * Processes commands from the client.
     */
    //@pure;
    private void processClientCommands() {
        try {
            greetClient();
            authenticateUser();

            while (true) {
                String command = socketIn.readLine();
                interpretAndProcess(command);
            }
        } catch (IOException | PlayerChatLacking | PlayerOfflineException e) {
            System.out.println("Client disconnected.");
            terminateConnection();
        }
    }

    /**
     * Interprets and processes a given command.
     * @param cmd The command string to interpret.
     */
    //@requires !cmd.isEmpty();
    //@pure;
    private void interpretAndProcess(String cmd) throws IOException, PlayerChatLacking, PlayerOfflineException {
        if (cmd == null) throw new IOException("Invalid command.");

        String[] parts = cmd.split("~");

        switch (parts[0].toUpperCase()) {
            case "QUEUE":
                handleQueueCommand();
                break;
            case "MOVE":
                handleMoveCommand(cmd);
                break;
            case "LIST":
                handleListCommand();
                break;
            case "RANK":
                handleRankCommand();
                break;
            case "CHAT":
                handleChatCommand(cmd);
                break;
            case "WHISPER":
                if (parts.length > 1) {
                    handleWhisperCommand(cmd, getClientName());
                } else {
                    System.out.println("No recipient name was indicated.");
                }
                break;
            case "CHALLENGE":
                handleChallengeCommand();
                break;
            default:
                Protocol.error(socketOut, "Unknown command");
                break;
        }

    }

    /**
     * Handles the queue command from the client.
     * @throws IOException If there's an error with input or output operations.
     */
    /*@ requires mainServer != null && socketOut != null;
        ensures mainServer.isInGame(clientName) == \old(mainServer.isInGame(clientName));
    */
    private void handleQueueCommand() throws IOException {
        if (mainServer.isInGame(clientName)) {
            Protocol.error(socketOut, "You are already in a game");
        } else {
            refreshPipedWriterReader();
            mainServer.switchQueue(this);
        }
    }

    /**
     * Handles the move command from the client.
     * @param cmd The move command to process.
     * @throws IOException If there's an error with input or output operations.
     */
    /*@ requires pWriter != null && cmd != null;
    */
    private void handleMoveCommand(String cmd) throws IOException {
        System.out.println("Sending response to client: " + cmd);

        pWriter.write(cmd + "\n");
        pWriter.flush();
    }

    /**
     * Sends a list of all users to the client.
     * @throws IOException If there's an error with input or output operations.
     */
    /*@ requires mainServer != null && socketOut != null;
    */
    private void handleListCommand() throws IOException {
        Protocol.sendList(socketOut, mainServer.getAllUsers());
    }

    /**
     * Sends the client's rank to them.
     * @throws IOException If there's an error with input or output operations.
     */
    //@ requires socketOut != null && mainServer != null;
    private void handleRankCommand() throws IOException {
        if (isRankingEnabled) {
            Protocol.sendRank(socketOut, mainServer.getRankings());
        } else {
            Protocol.error(socketOut, "Ranking not supported by your client.");
        }
    }

    /**
     * Handles the chat command from the client.
     * @param cmd The chat command to process.
     * @throws IOException If there's an error with input or output operations.
     */
    //@ requires socketOut != null && mainServer != null && cmd != null;
    private void handleChatCommand(String cmd) throws IOException {
        if (isChatEnabled) {
            String[] commands = cmd.split("~");
            if (commands.length < 2) {
                return;
            }
            mainServer.broadcastChatMessage(commands[1], clientName);
        } else {
            Protocol.error(socketOut, "Chat not supported by your client.");
        }
    }

    /**
     * Handles the whisper command from the client.
     * @param cmd The whisper command to process.
     * @param senderUsername The username of the sender.
     * @throws IOException If there's an error with input or output operations.
     * @throws PlayerChatLacking If the player lacks chat capability.
     * @throws PlayerOfflineException If the player is offline.
     */
    //@ requires socketOut != null && mainServer != null && cmd != null && senderUsername != null;
    public void handleWhisperCommand(String cmd, String senderUsername) throws IOException, PlayerChatLacking, PlayerOfflineException {
        if (isChatEnabled) {
            mainServer.whisper(cmd, senderUsername, socketOut);
        } else {
            Protocol.error(socketOut, "Whisper not supported by your client.");
        }
    }

    /**
     * Sends message to user.
     * @param message message to send
     * @param senderUsername username of the user
     */
    //@requires !message.isEmpty() && !senderUsername.isEmpty() && senderUsername.length() <= 20;
    //@pure;
    public void sendWhisper(String message, String senderUsername) {
        try {
            if (isChatEnabled()) {
                message = message.split("~")[2];
                Protocol.sendWhisper(socketOut, senderUsername, message);
            }
        } catch (IOException e) {
            System.out.println("Could not send whisper message");
        }
    }

    /**
     * Handles the challenge command from the client. The challenge feature is not supported.
     * @throws IOException If there's an error with input or output operations.
     */
    //@ requires socketOut != null;
    private void handleChallengeCommand() throws IOException {
        Protocol.error(socketOut, "Challenge feature not supported.");
    }

    /**
     * Authenticates the user.
     * @throws IOException If there's an error with input or output operations.
     */
    //@ requires socketIn != null;
    private void authenticateUser() throws IOException {
        while (true) {
            String loginCommand = socketIn.readLine();
            if (isValidLoginCommand(loginCommand)) break;
        }
    }

    /**
     * Checks if the command received is a valid login command and updates the client name.
     * @param cmd The command received from the client.
     * @return true if it's a valid login command, false otherwise.
     * @throws IOException If there's an error with input or output operations.
     */
    /*@ requires cmd != null;
        ensures \result == true || \result == false;
    */
    private boolean isValidLoginCommand(String cmd) throws IOException {
        if (cmd != null && cmd.startsWith("LOGIN")) {
            clientName = cmd.substring(6);
            if (mainServer.getAllUsers().contains(clientName)) {
                Protocol.sendALREADYLOGGEDIN(socketOut);
                return false;
            }
            if (clientName.length() > 20 || clientName.isEmpty() || clientName.contains("~")) {
                Protocol.error(socketOut, "Invalid username.");
                return false;
            }
            mainServer.addClient(this);
            notifyLoginSuccess();
            return true;
        }
        return false;
    }
    /**
     * Greets the client after they connect to the server.
     * @throws IOException If there's an error reading the greeting.
     */
    //@requires socketIn != null;
    private void greetClient() throws IOException {
        String greeting = socketIn.readLine();
        if (greeting.startsWith("HELLO")) {

            String[] features = greeting.split("~");
            setClientFeatures(features);
            sendWelcomeMessage();
        } else {

            terminateConnection();
        }
    }

    /**
     * Sets the features supported by the client.
     * @param features An array containing features sent by the client.
     */
    /*@ requires features != null;
        ensures isChatEnabled == (\exists int i; i >= 1 && i < features.length; features[i].equals("CHAT"));
    */
    private void setClientFeatures(String[] features) {
        for (int i = 1; i < features.length; i++) {
            switch (features[i]) {
                case "CHAT":
                    isChatEnabled = true;
                    break;
                case "RANK":
                    isRankingEnabled = true;
                    break;
                case "CHALLENGE":
                    isChallengeEnabled = true;
                    break;
                case "NOISE":
                    isNoiseEnabled = true;
                    break;
            }
        }
    }

    /**
     * Checks if the chat feature is enabled for the client.
     * @return true if chat is enabled, false otherwise.
     */
    //@pure;
    public boolean isChatEnabled() {
        return isChatEnabled;
    }

    /**
     * Returns the status of the chat feature.
     * @return true if chat is enabled, false otherwise.
     */
    //@pure;
    public boolean getChat() {
        return isChatEnabled;
    }

    /**
     * Sends a welcome message to the client.
     * @throws IOException If there's an error sending the message.
     */
    //@requires socketOut != null;
    private void sendWelcomeMessage() throws IOException {
        Protocol.hello(socketOut);
    }

    /**
     * Notifies the client about successful login.
     * @throws IOException If there's an error sending the notification.
     */
    //@requires socketOut != null;
    private void notifyLoginSuccess() throws IOException {
        Protocol.loggedIn(socketOut);
    }

    /**
     * Refreshes the piped writer and reader streams.
     * @throws IOException If there's an error with input or output operations.
     */
    /*@ requires pWriter != null && pReader != null; */
    private void refreshPipedWriterReader() throws IOException {
        pWriter.close();
        pReader.close();
        pWriter = new PipedWriter();
        pReader = new PipedReader(pWriter);
    }
}
