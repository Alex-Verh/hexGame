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

}
