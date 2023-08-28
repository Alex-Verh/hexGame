package server.controller;


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

    //@ ensures \result != null;
    //@ pure;
    public Socket getClientSocket() {
        return clientSocket;
    }

    //@ ensures !\result.isEmpty() && \result.length() <= 20;
    //@ pure;
    public String getClientName() {
        return clientName;
    }

    //@ ensures \result != null;
    //@ pure;
    public PipedReader getPipedReader() {
        return pReader;
    }

    //@ ensures \result != null;
    //@ pure;
    public BufferedWriter getSocketWriter() {
        return socketOut;
    }

    @Override
    public void run() {
        processClientCommands();
    }

    /**
     * Processes commands from the client.
     */
    private void processClientCommands() {
        try {
            greetClient();
            authenticateUser();

            while (true) {
                String command = socketIn.readLine();
                interpretAndProcess(command);
            }
        } catch (IOException e) {
            System.out.println("Client disconnected.");
            terminateConnection();
        }
    }

    /**
     * Interprets and processes a given command.
     * @param cmd The command string to interpret.
     */
    private void interpretAndProcess(String cmd) throws IOException {
        if (cmd == null) throw new IOException("Invalid command.");

        String[] parts = cmd.split("~");
        //DEBUGG
        System.out.println("FUll command : " + cmd + " first word: "+ parts[0]);
        //DEBUGG
        switch (parts[0].toUpperCase()) {
            case "QUEUE" -> handleQueueCommand();
            case "MOVE" -> handleMoveCommand(cmd);
            case "LIST" -> handleListCommand();
            case "RANK" -> handleRankCommand();
            case "CHAT" -> handleChatCommand(cmd);
            case "WHISPER" -> handleWhisperCommand(cmd, clientName);
            case "CHALLENGE" -> handleChallengeCommand();
            default -> Protocol.error(socketOut, "Unknown command");
        }
    }

    private void handleQueueCommand() throws IOException {
        if (mainServer.isInGame(clientName)) {
            Protocol.error(socketOut, "You are already in a game");
        } else {
            refreshPipedWriterReader();
            mainServer.switchQueue(this);
        }
    }

    private void handleMoveCommand(String cmd) throws IOException {
        System.out.println("Sending response to client: " + cmd);

        pWriter.write(cmd + "\n");
        pWriter.flush();
    }

    private void handleListCommand() throws IOException {
        Protocol.sendList(socketOut, mainServer.getAllUsers());
    }

    private void handleRankCommand() throws IOException {
        if (isRankingEnabled) {
            Protocol.sendRank(socketOut, mainServer.getRankings());
        } else {
            Protocol.error(socketOut, "Ranking not supported by your client.");
        }
    }

    private void handleChatCommand(String cmd) throws IOException {
        if (isChatEnabled) {
            mainServer.broadcastChatMessage(cmd, clientName);
        } else {
            Protocol.error(socketOut, "Chat not supported by your client.");
        }
    }

    public void handleWhisperCommand(String cmd, String username) throws IOException {
        if (isChatEnabled) {

            mainServer.sendPrivateMessage(cmd, username);

        } else {
            Protocol.error(socketOut, "Whisper not supported by your client.");
        }
    }

    private void handleChallengeCommand() throws IOException {
        Protocol.error(socketOut, "Challenge feature not supported.");
    }

    /**
     * Authenticates the user.
     */
    private void authenticateUser() throws IOException {
        while (true) {
            String loginCommand = socketIn.readLine();
            if (isValidLoginCommand(loginCommand)) break;
        }
    }

    /**
     * Checks if a given login command is valid.
     * @param cmd The login command string.
     * @return A boolean indicating if the command is valid.
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


    private void setClientFeatures(String[] features) {
        /////DEBUG/////
        System.out.println("Client joined: " + features[1]);
        ////////////////
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

    public boolean isChatEnabled() {
        return isChatEnabled;
    }

    /**
     * Gets the username.
     * @return username
     */
    //@ensures !\result.isEmpty() && \result.length() <= 20;
    //@pure;
    public String getName() {
        return clientName;
    }

    private void sendWelcomeMessage() throws IOException {
        Protocol.hello(socketOut);
    }

    private void notifyLoginSuccess() throws IOException {
        Protocol.loggedIn(socketOut);
    }

    private void refreshPipedWriterReader() throws IOException {
        pWriter.close();
        pReader.close();
        pWriter = new PipedWriter();
        pReader = new PipedReader(pWriter);
    }
}
