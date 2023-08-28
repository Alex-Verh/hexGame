package client.view;

import client.controller.*;
import client.model.*;

import java.io.*;
import java.net.Socket;
import java.util.List;
import java.util.Objects;

public class ClientTUI implements Runnable {

    private final BufferedReader clientBufferedReader;
    private final BufferedReader serverBufferedReader;
    private final Protocol protocol;
    private final String playerName;
    private final String playerType; // For AI or Human type.
    private boolean waiting;

    private static Socket socket;

    private static boolean chat = false;
    //@private invariant chat == false || chat == true;

    private static boolean rank = false;
    //@private invariant rank == false || rank == true;

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

    private static String getUsername(BufferedReader clientInput, Protocol protocol) throws IOException {
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

    private static String getPlayerType(BufferedReader clientInput) {

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
            System.out.println(game.getWinner() + " won");
        } else {
            System.out.println("Opponent has disconnected.");
            System.out.println("You have won by forfeit.");

        }
    }

    private Game gameInit(Board board, String data) {
        String[] split = data.split("~");
        Player player1;
        Player player2;
        System.out.println("DATA : " + data + " PLAYER NAME WE LOOK FOR: " + playerName);
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

    private Player createPlayer(Color color, Board board, String playerName) {
        if (playerType.equalsIgnoreCase("AI")) {
            return new AIPlayer(color, board, playerName, serverBufferedReader);
        } else {
            return new RealPlayer(color, board, playerName, clientBufferedReader, serverBufferedReader);
        }
    }

    private void clearReader(BufferedReader reader) throws IOException {
        while (reader.ready()) {
            reader.readLine();
        }
    }

    @Override
    public void run() {
        Board board = new Board();
        try {
            clearReader(serverBufferedReader);
            clearReader(clientBufferedReader);

            System.out.println("Waiting for opponent...");
            protocol.sendQueue();

            String data;
            while (true) {

                data = serverBufferedReader.readLine();
                if (data == null) {
                    System.err.println("Lost connection to the server.");
                    System.exit(1);  // or handle in some other appropriate way
                }
                if (data.startsWith("NEWGAME~")) {
                    break;
                }
                if (data.equals("QUEUE")) {

                    protocol.sendQueue();
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
     * sets connection to the server, sets the protocol.
     * and sets supported features
     * @return the protocol
     * @throws IOException if the socket fails
     */
    //@ensures \result != null;
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

