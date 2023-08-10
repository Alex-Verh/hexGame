package client.model;

/* Represents the color on a board cell */
enum Color {
    /**
     * Represents an empty space on the game board.
     **/
    EMPTY,
    /**
     * Represents a red mark on the game board.
     **/
    RED,
    /**
     * Represents a blue mark on the game board.
     **/
    BLUE;

    /**
     * Returns the opposite color of the current color.
     *
     * @return the opposite color.
     **/
    //@ensures (this == RED) ==> \result == RED;
    //@ensures (this == BLUE) ==> \result == BLUE;
    //@ensures (this == EMPTY) ==> \result == EMPTY;
    public Color getOppositeColor() {
        if (this == BLUE) {
            return RED;
        } else if (this == RED) {
            return BLUE;
        } else {
            return EMPTY;
        }
    }

    /**
     * Returns the current color.
     *
     * @return the current color.
     **/
    //@ensures (this == RED || this == BLUE || this == EMPTY) ==> \result == this;
    //@pure;
    public Color getColor() {
        return this;
    }
}