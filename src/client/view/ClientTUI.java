package client.view;

import client.sound.Sound;
import client.controller.*;
import client.model.*;

import java.io.*;
import java.net.Socket;
import java.util.List;

/**
 * A class that represents the Textual User Interface (TUI) for the client.
 * It provides the client with options to interact with a server.
 */
public class ClientTUI implements Runnable {

    private boolean waiting;
    //@private invariant waiting == true || waiting == false;

    private final BufferedReader clientBufferedReader;
    //@private invariant clientBufferedReader != null;

    private final BufferedReader serverBufferedReader;
    //@private invariant serverBufferedReader != null;

    private final Protocol protocol;
    //@private invariant protocol != null;

    private final String playerName;
    //@private invariant playerName.length() < 20 && playerName.length() > 1;

    private final String playerType; // For AI or Human type.
    //@private invariant !playerName.isEmpty();

    /**
     * Socket to manage the client-server connection.
     */
    private static Socket socket;
    //@private invariant socket != null;

    /**
     * Flag to determine if chat feature is supported by the server.
     */
    private static boolean chat = false;
    //@private invariant chat == false || chat == true;

    /**
     * Flag to determine if rank feature is supported by the server.
     */
    private static boolean rank = false;
    //@private invariant rank == false || rank == true;

    /**
     * Flag to determine if noise feature is supported by the server.
     */
    private static boolean noise = false;
    //@private invariant noise == false || noise == true;

    /**
     * Flag to determine if challenge feature is supported by the server.
     */
    private static boolean challenge = false;
    //@private invariant challenge == false || challenge == true;

    /**
     * Creates a new instance of the ClientTUI.
     *
     * @param clientReader Reader for the client input.
     * @param serverReader Reader for the server input.
     * @param protocol     The protocol to communicate with the server.
     * @param playerName   The name of the player.
     * @param playerType   Type of the player (AI or Human).
     */
    //@ requires clientReader != null && serverReader != null && protocol != null;
    //@ requires playerName != null && !playerName.isEmpty();
    //@ requires playerType.equals("AI") || playerType.equals("Human");
    //@ ensures this.clientBufferedReader != null && this.serverBufferedReader != null;
    //@ ensures this.protocol == protocol && this.playerName.equals(playerName) && this.playerType.equals(playerType);
    public ClientTUI(Reader clientReader, Reader serverReader, Protocol protocol, String playerName, String playerType) {
        this.serverBufferedReader = new BufferedReader(serverReader);
        this.clientBufferedReader = new BufferedReader(clientReader);
        this.protocol = protocol;
        this.playerName = playerName;
        this.playerType = playerType;
        this.waiting = true;
    }


    public static void main(String[] args) throws IOException {
        // We might want to gather some initialization parameters, perhaps from command-line arguments or a configuration.
        // For simplicity, let's assume hardcoded values.

        Reader clientReader = new InputStreamReader(System.in);  // Reading from standard input for simplicity
        BufferedReader clientInput = new BufferedReader(new InputStreamReader(System.in));


        // Prompt user for IP address
        System.out.print("Enter IP Address of the server (default: localhost): ");
        String serverIpAddress = clientInput.readLine();

        if (serverIpAddress.isEmpty()) {serverIpAddress = "localhost";}

        int portNumber = -1; // Initialize with an invalid value

        while (true) { // Keep asking until valid input is provided
            System.out.print("Enter port number (e.g. 8080): ");
            try {
                portNumber = Integer.parseInt(clientInput.readLine());
                if (portNumber < 0 || portNumber > 65535) {
                    System.out.println("Please enter a valid port number between 0 and 65535.");
                } else {
                    break;  // Break out of the loop if the port is valid
                }
            } catch (NumberFormatException e) {
                System.out.println("Please enter a valid port number.");
            }
        }

        try {
            System.out.println("Joining " + serverIpAddress + " on port " + portNumber);
            socket = new Socket(serverIpAddress, portNumber);
            Sound.backSound();
            Protocol protocol = setup(); // Assuming a default constructor for simplicity.

            PipedReader serverReader = new PipedReader();
            PipedWriter serverWriter = new PipedWriter(serverReader);
            Listener listener = new Listener(socket, serverWriter);
            String playerName = getUsername(clientInput, protocol);
            String playerType = getPlayerType(clientInput);

            Thread listnerthread = new Thread(listener);
            listnerthread.start();


            // Continuously read lines from System.in and send them to the server
            String line;
            printHelp();
            while (true) {
                line = clientInput.readLine();
                if (line.equalsIgnoreCase("QUIT")) { //if quit is typed break
                    System.exit(0);
                } else if (line.equalsIgnoreCase("HELP")) {
                    printHelp();
                } else if (line.equalsIgnoreCase("LIST")) {
                    protocol.sendList();
                } else if (line.equalsIgnoreCase("QUEUE")) {
                    ClientTUI gameTUI = new ClientTUI(clientReader, serverReader, protocol, playerName, playerType);
                    gameTUI.run();  // This will start the game
                    if (gameTUI != null && gameTUI.isWaiting()) {
                        serverWriter.write("QUEUE" + "\n");
                        serverWriter.flush();
                    } else {
                        System.out.println("You are already in a game");
                    }
                } else if (line.equalsIgnoreCase("RANK")) {
                    if (rank) {
                        protocol.sendRank();
                    } else {
                        System.out.println("Rank is not supported by the server");
                    }
                } else if (line.toUpperCase().startsWith("WHISPER")) {
                    if (chat) {
                        String[] split = line.split(" ");
                        if (split.length > 2) {
                            String name = split[1];
                            String message = line.substring(line.indexOf(name) + name.length() + 1);
                            protocol.sendWhisper(name, message);
                        } else {
                            System.out.println("Indicate the recipient and the actual message to him");
                        }
                    } else {
                        System.out.println("Chat is not supported by the server");
                    }
                } else {
                    if (chat) {
                        protocol.sendMessage(line);
                    } else {
                        System.out.println("Invalid command");
                    }
                }
            }
        } catch (IOException e) {
            System.out.println("This server is not working.");
        }
    }

    /**
     * Gets state of client if he is waiting or not.
     * @return true || false if client is waiting or not
     */
    //@ensures \result == true || \result == false;
    //@pure;
    public boolean isWaiting() {
        return waiting;
    }


    /**
     * Prints commands if asked.
     */
    //@pure;
    private static void printHelp() {
        System.out.println("\u001B[38;5;196m" + "Commands: \n" +
                "\u001B[38;5;51m" + "help" + "\u001B[0m" + " - shows this help message \n" +
                "\u001B[38;5;51m" + "quit" + "\u001B[0m" + " - quits the program\n" +
                "\u001B[38;5;51m" + "rank" + "\u001B[0m" + " - shows the rank of the players\n" +
                "\u001B[38;5;51m" + "list" + "\u001B[0m" + " - shows all users on the server\n" +
                "\u001B[38;5;51m" + "queue" + "\u001B[0m" + " - join the queue\n" +
                "\u001B[38;5;51m" + "whisper <name> <message>" + "\u001B[0m" + " - sends private message\n" +
                "or directly type" + "\u001B[38;5;51m" + " a message "+ "\u001B[0m" + "to send it to everyone\n" + "\u001B[0m");
    }

    public static String getUsername(BufferedReader clientInput, Protocol protocol) throws IOException {
        String playerName;
        BufferedReader reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        System.out.print("Enter your username:");
        while (true) { // Keep asking until valid input is provided
            playerName = clientInput.readLine(); // Player name

            if (playerName.isEmpty() || playerName.contains("~") || playerName.length() > 20) {
                System.out.println("Invalid name");
                continue;
            }
            if (protocol.sendUsername(playerName)) {
                String data = reader.readLine();
                // Check if the login was successful
                if (data.equals("LOGIN")) {
                    System.out.println("Logged in");
                    break;
                } else {
                    System.out.print("Error logging in. Try another username:");
                }
            } else {
                System.out.println("Failed to log in");
            }
        }
        return playerName;
    }

    /**
     * Gets the player type.
     *
     * @param clientInput The buffered reader to read user input.
     * @return The player type, either 'AI' or 'Human'.
     * @throws IOException if an I/O error occurs.
     * @requires clientInput != null.
     * @ensures \result.equals("AI") || \result.equals("Human");
     * @pure;
     */
    public static String getPlayerType(BufferedReader clientInput) {

        String playerType;

        while (true) { // Keep asking until valid input is provided
            System.out.print("Enter who will play for you: 'AI' or 'Human' ");
            try {
                playerType = clientInput.readLine(); // Player type: "AI" or "Human"
                if (!playerType.equalsIgnoreCase("ai") && !playerType.equalsIgnoreCase("human")) {
                    System.out.println("Please enter 'ai' or 'human'");
                } else {
                    break;  // Break out of the loop if the player type is valid
                }
            } catch (NumberFormatException | IOException e) {
                System.out.println("Please enter a valid option..");
            }
        }
        return playerType;
    }

    /**
     * Handles the game playing functionality.
     *
     * @param board The game board.
     * @param game The game instance to be played.
     * @requires board != null && game != null && !game.isFinished();
     */
    private void playGame(Board board, Game game) {
        while (!game.isFinished()) {
            board.displayBoard();
            System.out.println(((AbstractPlayer) game.getCurrentPlayer()).getName() + "'s turn");
            Move move =  game.getCurrentPlayer().move(game, protocol);
            if (game.isFinished() || move == null) {
                System.out.println("Game Over");
                break;
            }
            game.makeMove(move);
        }

        board.displayBoard();
        if (game.getWinner() != null) {
            System.out.println(((AbstractPlayer) game.getWinner()).getName() + " won");
            if (game.getWinner().toString().equals(playerName)) {
                Sound.winSound();
            } else {
                Sound.lostSound();
            }
        } else {
            System.out.println("Opponent has disconnected.");
            System.out.println("You have won by forfeit.");
            Sound.winSound();
        }
        printHelp();
    }

    /**
     * Initializes the game.
     *
     * @param board The game board.
     * @param data Data from the server to identify player names.
     * @return An instance of the initialized game.
     * @requires board != null && !board.isBoardFull() && data != null;
     * @ensures \result != null;
     */
    public Game gameInit(Board board, String data) {
        String[] split = data.split("~");
        Player player1;
        Player player2;
        if (split[1].equals(playerName)) {
            player1 = createPlayer(Color.RED, board, playerName);
            player2 = new NetworkPlayer(player1.getColor().getOppositeColor(), board, split[2], serverBufferedReader);

        } else {
            player1 = new NetworkPlayer(Color.RED, board, split[1], serverBufferedReader);
            player2 = createPlayer(player1.getColor().getOppositeColor(), board, playerName);
        }

        player1.setOpponent(player2);
        player2.setOpponent(player1);

        return new Game(board, player1, player2);
    }

    /**
     * Creates a player instance.
     *
     * @param color Color of the player.
     * @param board The game board.
     * @param playerName Name of the player.
     * @return The created player, either AIPlayer or RealPlayer.
     * @requires color != null && board != null && playerName != null;
     * @ensures \result != null;
     */
    private Player createPlayer(Color color, Board board, String playerName) {
        if (playerType.equalsIgnoreCase("AI")) {
            return new AIPlayer(color, board, playerName, serverBufferedReader);
        } else {
            return new RealPlayer(color, board, playerName, clientBufferedReader, serverBufferedReader);
        }
    }

    /**
     * Clears the BufferedReader.
     *
     * @param reader BufferedReader to be cleared.
     * @throws IOException if an I/O error occurs.
     * @requires reader != null;
     */
    private void clearReader(BufferedReader reader) throws IOException {
        while (reader.ready()) {
            reader.readLine();
        }
    }

    /**
     * Implementation of the Runnable interface's run method.
     */
    @Override
    public void run() {
        Board board = new Board();
        try {
            clearReader(serverBufferedReader);
            clearReader(clientBufferedReader);

            System.out.println("Waiting for opponent... Type 'queue' again to exit.");
            Sound.shot();
            protocol.sendQueue();

            String data;
            while (true) {
                // Check if there's any data from the server
                while (!serverBufferedReader.ready()) {
                    if (clientBufferedReader.ready()) {
                        String userInput = clientBufferedReader.readLine();
                        if ("queue".equalsIgnoreCase(userInput)) {
                            System.out.println("You quited the queue.");

                            Sound.shot();
                            protocol.sendQueue();
                            return;
                        }
                    }
                }

                data = serverBufferedReader.readLine();
                if (data == null) {
                    System.err.println("Lost connection to the server.");
                    System.exit(1);  // or handle in some other appropriate way
                }
                if (data.startsWith("NEWGAME~")) {
                    Sound.startSound();
                    break;
                }
                if (data.equals("QUEUE")) {
                    protocol.sendQueue();
                    Sound.shot();
                    System.out.println("Left the queue");
                    return;
                }

            }
            waiting = false;


            Game game = gameInit(board, data);
            playGame(board, game);

        } catch (IOException e) {
            System.out.println("Could not connect to server");
            System.exit(1);
        }
    }


    /**
     * Sets up communication protocol.
     *
     * @return Initialized protocol for communication.
     * @throws IOException if connection to the server fails.
     * @ensures \result != null;
     */
    private static Protocol setup() throws IOException {


        BufferedReader reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        Protocol protocol = new Protocol(socket);

        // Send a "HELLO" message to the server
        if (protocol.sendHello()) {
            // Check if the server has sent a "HELLO" message back
            String data = reader.readLine();
            if (data.startsWith("HELLO")) {
                List<String> list = List.of(data.split("~"));
                if (list.contains("CHAT")) {
                    chat = true;
                }
                if (list.contains("RANK")) {
                    rank = true;
                }
                System.out.println("Connected to server");
            } else {
                System.out.println("Error connecting to server");
                System.exit(0);
            }
        } else {
            System.out.println("Failed to connect to server");
            System.exit(0);
        }
        return protocol;
    }
}

