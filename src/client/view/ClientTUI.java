package client.view;

import client.controller.AIPlayer;
import client.controller.NetworkPlayer;
import client.controller.Protocol;
import client.controller.RealPlayer;
import client.model.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.net.Socket;

public class ClientTUI implements Runnable {

    private final BufferedReader clientBufferedReader;
    private final BufferedReader serverBufferedReader;
    private final Protocol protocol;
    private final String playerName;
    private final String playerType; // For AI or Human type.
    private boolean waiting;

    public ClientTUI(Reader clientReader, Reader serverReader, Protocol protocol, String playerName, String playerType) {
        this.serverBufferedReader = new BufferedReader(serverReader);
        this.clientBufferedReader = new BufferedReader(clientReader);
        this.protocol = protocol;
        this.playerName = playerName;
        this.playerType = playerType;
        this.waiting = true;
    }

    public boolean isWaiting() {
        return waiting;
    }
    public static void main(String[] args) throws IOException {
        // We might want to gather some initialization parameters, perhaps from command-line arguments or a configuration.
        // For simplicity, let's assume hardcoded values.

        Reader clientReader = new InputStreamReader(System.in);  // Reading from standard input for simplicity
        Reader serverReader; // This must be connected to the server somehow.
        String playerName = "JohnDoe";      // Hardcoded player name for the example
        String playerType = "Human";        // Player type: "AI" or "Human"

        try {
            Socket serverSocket = new Socket("130.89.253.64", 44445);
            Protocol protocol = new Protocol(serverSocket); // Assuming a default constructor for simplicity.
            serverReader = new BufferedReader(new InputStreamReader(serverSocket.getInputStream()));
            ClientTUI gameTUI = new ClientTUI(clientReader, serverReader, protocol, playerName, playerType);
            gameTUI.run();  // This will start the game
        } catch (IOException e) {
            System.err.println(e);
        }
    }


    public void run() {
        play();
    }

    private void play() {
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
                if (data.startsWith("NEWGAME")) {
                    break;
                }
                if (data.equals("QUEUE")) {
                    protocol.sendQueue();
                    System.out.println("Left the queue");
                    return;
                }
            }

            waiting = false;

            Game game = setup(board, data);
            playGame(board, game);

        } catch (IOException e) {
            System.out.println("Could not connect to server");
            System.exit(1);
        }
    }

    private void playGame(Board board, Game game) {
        while (!game.isFinished()) {
            System.out.println(board);
            System.out.println(game.getCurrentPlayer() + "'s turn");

            Move move = game.getCurrentPlayer().move(game, protocol);

            if (game.isFinished()) {
                System.out.println("Game Over");
                break;
            }

            game.makeMove(move);
        }

        System.out.println(board);
        if (game.getWinner() != null) {
            System.out.println(game.getWinner() + " won");
        } else if (game.isFinished()) {
            System.out.println("Draw");
        } else {
            System.out.println("Player has disconnected");
        }
    }

    private Game setup(Board board, String data) {
        String[] split = data.split("~");
        Player player1;
        Player player2;

        if (split[1].equals(playerName)) {
            player1 = createPlayer(Color.RED, board, playerName);
            player2 = new NetworkPlayer(Color.BLUE, board, split[2], serverBufferedReader);
        } else {
            player1 = new NetworkPlayer(Color.BLUE, board, split[1], serverBufferedReader);
            player2 = createPlayer(Color.RED, board, playerName);
        }

        player1.setOpponent(player2);
        player2.setOpponent(player1);

        return new Game(board, player1, player2);
    }

    private Player createPlayer(Color color, Board board, String playerName) {
        if (playerType.equals("AI")) {
            return new AIPlayer(color, board, playerName, clientBufferedReader);
        } else {
            return new RealPlayer(color, board, playerName, clientBufferedReader, serverBufferedReader);
        }
    }

    private void clearReader(BufferedReader reader) throws IOException {
        while (reader.ready()) {
            reader.readLine();
        }
    }
}

