package client.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The Game class this is class has all the logic for the game.
 */
public class Game {
    private final Board board;
    //@private invariant !board.isBoardFull() && board != null;

    private final Player player1;
    /*@private invariant player1.getColor() != Color.EMPTY
            && player1.getOpponent() != null && player1 != null; */

    private final Player player2;
    /*@private invariant player2.getColor() != Color.EMPTY
            && player2.getOpponent() != null && player2 != null; */

    private Player currentPlayer;
    /*@private invariant currentPlayer.getColor() != Color.EMPTY
            && currentPlayer.getOpponent() != null && currentPlayer != null; */

    /**
     * Creates a new game.
     * @param board the board of the game
     * @param player1 the first player
     * @param player2 the second player
     */
    /*@requires !getBoard().isBoardFull() && getBoard() != null
            && player1.getColor() != Color.EMPTY && player1.getOpponent() != null
                    && player1 != null && player2.getColor() != Color.EMPTY
                            && player2.getOpponent() != null && player2 != null; */
    public Game(Board board, Player player1, Player player2) {
        this.board = board;
        this.player1 = player1;
        this.player2 = player2;
        this.currentPlayer = player1;
    }

    /**
     * Gets the board.
     * @return board
     */
    //@ensures \result != null && \result.SIZE > 0;
    //@pure;
    public Board getBoard() {
        return board;
    }

    /**
     * Gets player that has to move at the moment.
     * @return currentPlayer that has to move
     */
    //@ensures \result == player1 || \result == player2;
    //@pure;
    public Player getCurrentPlayer() {
        return currentPlayer;
    }

    /**
     * Switch to the next player.
     */
    private void switchCurrentPlayer() {
        currentPlayer = (currentPlayer == player1) ? player2 : player1;
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
     * Gets a list of valid moves for the current player.
     * @return list of valid moves.
     */
    //@ensures \result != null;
    //@pure
    public List<Move> getValidMoves() {
        List<Move> validMoves = new ArrayList<>();
        List<Integer> fieldColored = countFields();
        // Check if it is second move
        if (fieldColored.get(0) <= 1 && fieldColored.get(1) == 0 && currentPlayer.getColor() == Color.BLUE) {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
            // Add a swap possibility if it is a second move
            validMoves.add(new Move(9, 0, currentPlayer.getColor()));  // Special Move for swap
        } else {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
        }
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
                    validMoves.add(new Move(row, col, currentPlayer.getColor()));
                }
            }
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
                            switchCurrentPlayer();
                            return;
                        }
                    }
                }
                System.out.println("No RED piece to be swapped!");
            }
            //DEBUG//
            System.out.println("Move to be made: " + move + " by : " + move.getColor());
            //DEBUG//

            // Place the player's color on the board
            board.setField(move.getRow(), move.getCol(), move.getColor());
            switchCurrentPlayer();
        } else {
            System.out.println("Illegal Move.");
        }
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
    public Player getWinner() {
        // Check for a winning path for Player 1 (assume they connect top to bottom)
        for (int col = 0; col < Board.SIZE; col++) {
            if (board.getFieldColor(0, col) == player1.getColor()) {
                if (dfs(0, col, player1.getColor(), new boolean[Board.SIZE][Board.SIZE])) {
                    return player1;
                }
            }
        }

        // Check for a winning path for Player 2 (assume they connect left to right)
        for (int row = 0; row < Board.SIZE; row++) {
            if (board.getFieldColor(row, 0) == player2.getColor()) {
                if (dfs(row, 0, player2.getColor(), new boolean[Board.SIZE][Board.SIZE])) {
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

        if ((color == player1.getColor() && row == Board.SIZE - 1) || (color == player2.getColor() && col == Board.SIZE - 1)) {
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
     * Returns a copy of the game.
     * @return the copy of the game
     */
    //@ensures \result != this;
    /*@requires !this.getBoard().isBoardFull() && this.getBoard() != null &&
        this.player1.getColor() != Color.EMPTY && this.player1.getOpponent() != null &&
            this.player1 != null && this.player2.getColor() != Color.EMPTY &&
                this.player2.getOpponent() != null && this.player2 != null; */
    public Game deepCopy() {
        Board newBoard = board.deepCopy();
        Player newPlayer1 = player1.deepCopy();
        Player newPlayer2 = player2.deepCopy();
        Game copyGame = new Game(newBoard, newPlayer1, newPlayer2);
        copyGame.currentPlayer = currentPlayer;
        return copyGame;
    }

}