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
     * Counts the number of red and blue fields on the board.
     * @return A list where the first integer is the count of red fields
     * and the second integer is the count of blue fields.
     */
    public List<Integer> countFields() {
        int redFieldsCounter = 0;
        int blueFieldsCounter = 0;
        for (int row = 0; row < Board.SIZE; row++) {
            for (int col = 0; col < Board.SIZE; col++) {
                if (board.getFieldColor(row + 1, col + 1) == Color.RED) { // Adding 1 to row and col because getFieldColor expects 1-based indices.
                    redFieldsCounter++;
                } else if (board.getFieldColor(row + 1, col + 1) == Color.BLUE) {
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
        if (fieldColored.get(0) <= 1 && fieldColored.get(1) == 0) {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
            // Add a swap possibility if it is a second move
            validMoves.add(new Move(-1, -1, currentPlayer.getColor()));  // Special Move for swap
        } else {
            // Add empty fields to valid moves
            addValidMoves(validMoves);
        }
        return validMoves;
    }

    /**
     * Add valid moves for empty fields for current player
     * @param validMoves
     */
    private void addValidMoves(List<Move> validMoves) {
        for (int row = 0; row < Board.SIZE; row++) {
            for (int col = 0; col < Board.SIZE; col++) {
                if (board.isFieldEmpty(row + 1, col + 1)) {  // adjusting to 1-indexed
                    validMoves.add(new Move(row, col, currentPlayer.getColor()));
                }
            }
        }
    }
}