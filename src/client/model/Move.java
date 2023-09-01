package client.model;

/**
 * Represents a move in the Hex game.
 */
public class Move {


    private final int row;
    //@private invariant row >= 0 && row < Board.SIZE;

    private final int col;
    //@private invariant col >= 0 && col < Board.SIZE;

    private final Color color;
    //@private invariant color == Color.EMPTY || color == Color.BLUE || color == Color.RED;

    /**
     * Constructs a new move.
     *
     * @param row The row where the move was made.
     * @param col The column where the move was made.
     * @param color The color of the player making the move.
     **/
    //@requires (row >= 0 && row < Board.SIZE) || row == 9;
    //@requires col >= 0 && col < Board.SIZE;
    //@requires color != null;
    public Move(int row, int col, Color color) {
        if(row < 0 || (row >= Board.SIZE && row != 9) || col < 0 || col >= Board.SIZE) {
            throw new IllegalArgumentException("Row or column out of range");
        }
        if(color == null) {
            throw new IllegalArgumentException("Color cannot be null");
        }
        this.row = row;
        this.col = col;
        this.color = color;
    }

    /**
     * Returns the row of this move.
     *
     * @return The row.
     **/
    //@pure
        public int getRow() {
        return row;
    }

    /**
     * Returns the column of this move.
     *
     * @return The column.
     **/
    //@pure
    public int getCol() {
        return col;
    }

    /**
     * Returns the color of the player making this move.
     *
     * @return The player's color.
     **/
    //@pure
    public Color getColor() {
        return color;
    }

    /**
     * Returns move information
     *
     * @return moveInfo
     */
    //@pure;
    @Override
    public String toString() {
        int index = hashCode();
        return String.format("Move {Index: %d, Row: %d, Col: %d, Mark: %s}", index, row, col, color);
    }

    /**
     * Generates a unique integer value for the move, based on its row and column.
     * @return identifier
     */
    //@ensures \result == (getRow()) * Board.SIZE + (getCol());
    //@pure;
    @Override
    public int hashCode() {
        return (row) * Board.SIZE+ (col);
    }

    /**
     * Compares move to another move.
     * @param o move to compare to
     * @return true || false
     */
    //@requires o != null;
    //@requires o instanceof Move;
    /*@ensures \result == (this.getColor() == ((Move) o).getColor() &&
            this.getCol() == ((Move) o).getCol() && this.getRow() == ((Move) o).getRow()); */
    //@pure;
    @Override
    public boolean equals(Object o) {
        if (o instanceof Move) {
            Move m = (Move) o;
            return m.getCol() == col && m.getRow() == row && m.getColor() == color;
        }
        return false;
    }
}
