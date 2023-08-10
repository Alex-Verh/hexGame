package client.model;

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
}