package client.model;

/**
 * Abstract Player that implements Player interface.
 */
public class AbstractPlayer implements Player {
    private final Color color;
    //@private invariant color != null;

    private Player opponent;
    //@private invariant opponent != null && opponent.getOpponent() != null;

    private final Board board;
    /*@private invariant (\forall int i; (i >= 0 && i < Board.SIZE*Board.SIZE);
                            board.getFieldColor(i/Board.SIZE, i%Board.SIZE) == Color.EMPTY);    */

    private final String name;
    //@private invariant !name.isEmpty();

    /**
     * Creates a new AbstractPlayer player.
     * @param color the color of the pl ayer
     * @param board the board of the game
     * @param name the name of the player
     */
    //@requires color == Color.EMPTY || color == Color.BLUE || color == Color.RED;
    //@requires (\forall int i; (i >= 0 && i < board.SIZE * board.SIZE); board.getFieldColor(i/board.SIZE, i%board.SIZE) != Color.EMPTY);
    public AbstractPlayer(Color color, Board board, String name) {
        this.color = color;
        this.board = board;
        this.name = name;
    }

    /**
     * Returns the color associated with this player.
     *
     * @return the color of the player.
     **/
    //@ensures \result == Color.RED || \result == Color.BLUE || \result == Color.EMPTY;
    //@pure;
    @Override
    public Color getColor() {
        return color;
    }

    /**
     * Sets the opponent of this player.
     *
     * @param opponent The opponent player.
     **/
    //@requires opponent != null;
    //@ensures opponent == this.getOpponent();
    @Override
    public void setOpponent(Player opponent) {
        this.opponent = opponent;
    }

    /**
     * Returns the opponent of this player.
     *
     * @return The opponent player.
     **/
    //@ensures \result != null || \result.getOpponent() == this;
    //@pure;
    @Override
    public Player getOpponent() {
        return opponent;
    }

    /**
     * Returns the board of this player.
     *
     * @return The board.
     **/
    //@ensures \result != null;
    //@pure;
    @Override
    public Board getBoard() {
        return board;
    }

    /**
     * This method is called when it is this player's turn to make a move.
     *
     * @param game the game that is being played
     * @return the move that this player wants to make
     */
    @Override
    public Move move(Game game) {
        return null;
    }

    /**
     * Copies a player.
     *
     * @return player copy
     */
    @Override
    public Player deepCopy() {
        Player player = new AbstractPlayer(color, board, name);
        player.setOpponent(opponent);
        return player;
    }

    /**
     * Returns the name of this player.
     *
     * @return The name.
     **/
    //@ensures \result != null;
    //@pure;
    public String getName() {
        return name;
    }
}
