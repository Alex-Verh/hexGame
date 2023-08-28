package server.model;

import client.model.Board;
import client.model.Color;
import client.model.Move;
import client.model.Player;
import server.controller.ClientHandler;
import server.controller.Protocol;
import server.controller.Server;

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * The Game class this is the game class that handles all the game logic.
 */
public class GameServer implements Runnable {

    private final BufferedWriter writer1;
    //@private invariant writer1 != null;

    private final BufferedWriter writer2;
    //@private invariant writer2 != null;

    private final BufferedReader reader1;
    //@private invariant reader1 != null;

    private final BufferedReader reader2;
    //@private invariant reader2 != null;

    private final String player1;
    //@private invariant !player1.isEmpty() && player1.length() <= 20;

    private final String player2;
    //@private invariant !player2.isEmpty() && player2.length() <= 20;

    private final Board board;
    //@private invariant board != null;

    private final Server server;
    //@private invariant server != null;


    /**
     * Creates a new Game.
     * @param player1 - player 1
     * @param player1 - player 2
     * @param server the server
     */
    //@requires player1 != null && player2 != null;
    public GameServer(ClientHandler player1, ClientHandler player2, Server server) {
        this.server = server;
        board = new Board();
        this.writer1 = player1.getSocketWriter();
        this.writer2 = player2.getSocketWriter();
        this.reader1 = new BufferedReader(player1.getPipedReader());
        this.reader2 = new BufferedReader(player2.getPipedReader());
        this.player1 = player1.getName();
        this.player2 = player2.getName();
    }

    /**
     * Gets the board.
     * @return the board
     */
    //@ensures \result == board;
    //@pure;
    public Board getBoard() {
        return board;
    }

    /**
     * Make a move on the board.
     *
     * @param move The move to be made.
     */
    public void makeMove(Move move) {
        // Check if move is valid
        if (move != null && isValidMove(move)) {


            // Check if the move is a special swap move
            if (move.getRow() == 9 && move.getCol() == 0 && move.getColor() == Color.BLUE) {
                // Get the position of the RED piece on the board (assuming there's only one, since it's the second move)
                for (int i = 0; i < Board.SIZE; i++) {
                    for (int j = 0; j < Board.SIZE; j++) {
                        if (board.getFieldColor(i, j) == Color.RED) {
                            board.swapField(i, j);
                            return;
                        }
                    }
                }
                System.out.println("No RED piece to be swapped!");
            }


            // Place the player's color on the board
            board.setField(move.getRow(), move.getCol(), move.getColor());
        } else {
            System.out.println("Illegal Move.");
        }
    }


    /**
     * Checks if a move is valid
     * @param move that is checked
     * @return true || false
     */
    public boolean isValidMove(Move move) {
        for (Move validMove : getValidMoves()) {
            if (validMove.hashCode() == move.hashCode()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Gets a list of valid moves for the current player.
     * @return list of valid moves.
     */
    //@ensures \result != null;
    //@pure
    public List<Move> getValidMoves() {
        List<Move> validMoves = new ArrayList<>();
        List<Integer> fieldColored = countFields();
        // Check if it is second move
        if (fieldColored.get(0) <= 1 && fieldColored.get(1) == 0) {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
            // Add a swap possibility if it is a second move
            validMoves.add(new Move(9, 0,  Color.EMPTY));  // Special Move for swap
        } else {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
        }
        //DEBUG
        System.out.println(validMoves);
        //////
        return validMoves;
    }

    /**
     * Add valid moves for empty fields for current player
     * @param validMoves - list of valid moves
     */
    private void addValidMoves(List<Move> validMoves) {
        validMoves.clear();
        for (int row = 0; row < Board.SIZE; row++) {
            for (int col = 0; col < Board.SIZE; col++) {
                if (board.isFieldEmpty(row, col)) {  // adjusting to 1-indexed
                    validMoves.add(new Move(row, col, Color.EMPTY));
                }
            }
        }
    }

    /**
     * Counts the number of red and blue fields on the board.
     * @return A list where the first integer is the count of red fields
     * and the second integer is the count of blue fields.
     */
    public List<Integer> countFields() {
        int redFieldsCounter = 0;
        int blueFieldsCounter = 0;
        for (int row = 0; row < Board.SIZE; row++) {
            for (int col = 0; col < Board.SIZE; col++) {
                if (board.getFieldColor(row, col) == Color.RED) { // Adding 1 to row and col because getFieldColor expects 1-based indices.
                    redFieldsCounter++;
                } else if (board.getFieldColor(row, col) == Color.BLUE) {
                    blueFieldsCounter++;
                }
            }
        }
        return Arrays.asList(redFieldsCounter, blueFieldsCounter);
    }

    /**
     * Checks if game is finished.
     * @return true || false if game is over or not
     */
    //@ensures getBoard().isBoardFull() || getValidMoves().isEmpty();
    //@pure;
    public boolean isFinished() {
        return board.isBoardFull() || getValidMoves().isEmpty() || (getWinner() == player1 || getWinner() == player2);
    }



    /**
     * Gets the winner of the game, decided by a connection of hexagons between vertical and horizontal lines.
     * Uses Depth First Search (DFS) to determine if a player has a winning path from one side of the board to the other.
     *
     * @return the winning player if one exists, null otherwise
     */
    //@ ensures \result == player1 || \result == player2 || \result == null;
    //@ pure;
    public String getWinner() {
        // Check for a winning path for Player 1 (assume they connect top to bottom)
        for (int col = 0; col < Board.SIZE; col++) {
            if (board.getFieldColor(0, col) == Color.RED) {
                if (dfs(0, col, Color.RED, new boolean[Board.SIZE][Board.SIZE])) {
                    return player1;
                }
            }
        }

        // Check for a winning path for Player 2 (assume they connect left to right)
        for (int row = 0; row < Board.SIZE; row++) {
            if (board.getFieldColor(row, 0) == Color.BLUE) {
                if (dfs(row, 0, Color.BLUE, new boolean[Board.SIZE][Board.SIZE])) {
                    return player2;
                }
            }
        }

        return null;
    }

    /**
     * Depth First Search (DFS) to check if the specified color has a winning path on the board.
     * The DFS starts from the given row and col and explores possible paths in depth to check if the player with the specified color has a winning path.
     *
     * @param row The starting row of the DFS.
     * @param col The starting column of the DFS.
     * @param color The color for which we are checking the path.
     * @param visited A 2D boolean array that keeps track of which board positions have already been visited in this DFS.
     * @return true if the color has a winning path starting from the given row and col, false otherwise.
     */
    //@ requires 0 <= row && row < Board.SIZE && 0 <= col && col < Board.SIZE;
    //@ requires color != null && color != Color.EMPTY;
    //@ requires visited != null && visited.length == Board.SIZE && (\forall int i; 0 <= i && i < Board.SIZE; visited[i].length == Board.SIZE);
    //@ ensures \result == true || \result == false;
    //@ pure;
    private boolean dfs(int row, int col, Color color, boolean[][] visited) {
        if (row < 0 || col < 0 || row >= Board.SIZE || col >= Board.SIZE) {
            return false;
        }

        if (board.getFieldColor(row, col) != color || visited[row][col]) {
            return false;
        }

        if ((color == Color.RED && row == Board.SIZE - 1) || (color == Color.BLUE && col == Board.SIZE - 1)) {
            return true;
        }

        visited[row][col] = true;

        int[][] directions = {
                {-1, 0}, {1, 0}, {0, -1}, {0, 1}, {-1, 1}, {1, -1}
        };

        for (int[] direction : directions) {
            int newRow = row + direction[0];
            int newCol = col + direction[1];

            if (dfs(newRow, newCol, color, visited)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Runnable class for the game server this handles the 2 clients games.
     */
    //@pure;
    @Override
    public void run() {
        start();
    }

    //@pure;
    private void start() {
        //clear the readers/writers
        if (clearReader(reader1)) {
            return;
        }
        if (clearReader(reader2)) {
            return;
        }

        boolean disconnected;
        //sends start message to both players
        newGame(writer1);
        newGame(writer2);

        while (true) {
            disconnected = gamePlay(reader1, Color.RED, writer1);

            if (gameOverMessage()) {
                break;
            }

            // If red player disconnected
            if (disconnect(disconnected)) {
                break;
            }

            disconnected = gamePlay(reader2, Color.BLUE, writer2);

            if (gameOverMessage()) {
                break;
            }

            // If blue player disconnected
            if (disconnect(disconnected)) {
                break;
            }
        }

        try {
            reader1.close();
        } catch (IOException e) {
            System.out.println("Error closing first player reader");
        }
        try {
            reader2.close();
        } catch (IOException e) {
            System.out.println("Error closing second player reader");
        }
    }

    /**
     * starts a new game. Sends a new game message to both players.
     * @param writer the writer to send the message to
     */
    //@requires writer != null;
    //@pure;
    private void newGame(BufferedWriter writer) {
        try {
            Protocol.sendNewGame(writer, player1, player2);
        } catch (IOException e) {
            System.out.println("Error sending new game message");
        }
    }

    /**
     * Constantly clears reader.
     * @param reader the reader to clear
     * @return true || false
     */
    //@requires reader != null;
    //@ensures \result == !reader.readLine().isEmpty();
    private boolean clearReader(BufferedReader reader) {
        // clear BufferedReader for both players
        while (true) {
            try {
                if (!reader.ready()) { // check if reader has any data
                    break;
                }
                reader.readLine(); // read and discard data if present
            } catch (IOException e) {
                System.out.println("Error clearing Reader");
                return true;
            }
        }
        return false;
    }

    /**
     * Gameplay method with move evaluator.
     * @param reader the reader to read from
     * @param color the mark to check for
     * @param writer the writer to write to
     * @return true || false
     */
    //@requires reader != null && writer != null;
    //@requires color == Color.RED && color == Color.BLUE && color == Color.EMPTY;
    //@ensures \result == false || \result == true;
    private boolean gamePlay(BufferedReader reader, Color color, BufferedWriter writer) {
        boolean disconnect = false;
        while (true) {
            try {
                String data = reader.readLine();
                if (data != null) {
                    if (data.contains("MOVE")) {
                        String[] parts = data.split("~");
                        int index = Integer.parseInt(parts[1]);
                        int row = index / Board.SIZE;
                        int col = index % Board.SIZE;
                        Move move = new Move(row, col, color);

                        if (isValidMove(move)) {
                            makeMove(move);
                            Protocol.sendMove(writer1, index);
                            Protocol.sendMove(writer2, index);
                        } else {
                            Protocol.error(writer, "Invalid move");
                            disconnect = true;
                        }
                        break;
                    }
                } else {
                    throw new IOException();
                }
            } catch (IOException e) {
                disconnect = true;
                break;
            }
        }
        return disconnect;
    }

    /**
     * Sends final message if game is over.
     * @return true || false
     */
    //@ensures \result == isFinished();
    //@pure;
    private boolean gameOverMessage() {
        // check if the game is over if so then send the end message VICTORY or DRAW
        if (isFinished()) {
            server.removeGameServer(this);
            finalMessage(writer1);
            finalMessage(writer2);
            return true;
        }
        return false;
    }

    /**
     * Sends final message.
     * @param writer the writer to send the message to
     */
    //@requires writer != null;
    //@pure;
    private void finalMessage(BufferedWriter writer) {
        try {
            if (Objects.equals(getWinner(), player1)) {
                Protocol.victory(writer, player1);
            } else if (Objects.equals(getWinner(), player2)) {
                Protocol.victory(writer, player2);
            } else {
                Protocol.draw(writer);
            }
        } catch (IOException e) {
            System.out.println("Error sending game over message");
        }
    }

    /**
     * Sends message if disconnected.
     * @param gameOver if game is over
     * @return true || false
     */
    //@requires gameOver == true || gameOver == false;
    //@requires writer1 != null && !player1.isEmpty() && player1.length() <= 20;
    //@requires writer2 != null && !player2.isEmpty() && player2.length() <= 20;
    //@ensures \result == gameOver;
    //@pure;
    private boolean disconnect(boolean gameOver) {
        // if one player has disconnected then send the end message to both players
        if (gameOver) {
            server.removeGameServer(this);
            try {
                Protocol.disconnect(writer1, player1);
                Protocol.disconnect(writer2, player2);
            } catch (IOException e) {
                System.out.println("Error sending disconnect message");
            }

            // Terminate the game session
            return true;
        }
        return false;
    }


    /**
     * Returns the players.
     * @return the players
     */
    //@pure;
    public List<String> getPlayers() {
        List<String> players = new ArrayList<>();
        players.add(player1);
        players.add(player2);
        return players;
    }
}
