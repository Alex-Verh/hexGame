package client.model;

public interface Player {

    /**
     * Returns the color associated with this player.
     *
     * @return the color of the player.
     **/
    //@pure
    Color getColor();

    /**
     * Sets the opponent of this player.
     *
     * @param opponent The opponent player.
     **/
    //@requires opponent != null && opponent != this;
    //@ensures getOpponent() == opponent;
    void setOpponent(Player opponent);

    /**
     * Returns the opponent of this player.
     *
     * @return The opponent player.
     **/
    //@pure
    Player getOpponent();

    /**
     * Returns the board of this player.
     *
     * @return The board.
     **/
    //@ensures \result != null;
    //@pure;
    Board getBoard();

    /**
     * This method is called when it is this player's turn to make a move.
     * @param game the game that is being played
     * @return the move that this player wants to make
     */
    //@requires game != null;
    //@requires game.getBoard() != null && !game.isFinished();
    //@ensures game.getValidMoves().contains(\result);
    Move move(Game game);

}
