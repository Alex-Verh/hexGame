package client.model;

public class Board {
    public static final int SIZE = 9;
    //@public invariant SIZE > 0;


    /* ANSI Color codes for console display */
    private static final String ANSI_RESET = "\u001B[0m";
    private static final String ANSI_BLUE = "\u001B[34m";
    private static final String ANSI_GREEN = "\u001B[38;5;34m";
    private static final String ANSI_RED = "\u001B[38;5;88m";

    private Color[][] board;
    //@private invariant board != null;

    //@ensures board.length == SIZE;
    //@ensures (\forall int i; 0 <= i && i < SIZE; (\forall int j; 0 <= j && j < SIZE; board[i][j] == Color.EMPTY));
    public Board() {
        board = new Color[SIZE][SIZE];
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                board[row][col] = Color.EMPTY;
            }
        }
    }

    /* Prints the board with appropriate colors */
    public void displayBoard() {
        int size = SIZE;
        System.out.println(ANSI_RED + "====================================================================" + ANSI_RESET);

        for (int row = 0; row < size; row++) {
            String indent = " ".repeat(row * 2);
            String rightPadding = "  ".repeat(size - row); // This will pad to the right

            System.out.print(ANSI_BLUE + "║ " + ANSI_RESET); // Left border

            if (row == 0) {
                System.out.print(indent);
                for (int col = 0; col < size; col++) {
                    System.out.print(" ");
                    System.out.print("/‾‾\\");
                }
                System.out.print(rightPadding); // Added for the right alignment
                System.out.println(ANSI_BLUE + "  ║" + ANSI_RESET); // Right border
                System.out.print(ANSI_BLUE + "║ " + ANSI_RESET); // Left border
            }

            System.out.print(indent);

            for (int col = 0; col < size; col++) {
                int index = row * size + col;
                switch (board[row][col]) {
                    case RED:
                        System.out.print("| " + ANSI_RED + "RR" + ANSI_RESET + " ");
                        break;
                    case BLUE:
                        System.out.print("| " + ANSI_BLUE + "BB" + ANSI_RESET + " ");
                        break;
                    default:
                        System.out.print("| " + ANSI_GREEN + String.format("%02d", index) + ANSI_RESET + " ");
                        break;
                }
            }
            System.out.print("|");
            System.out.print(rightPadding); // Added for the right alignment
            System.out.println(ANSI_BLUE + " ║" + ANSI_RESET); // Right border
            System.out.print(ANSI_BLUE + "║ " + ANSI_RESET); // Left border
            System.out.print(indent + " ");

            for (int col = 0; col < size; col++) {
                System.out.print("\\__/‾");
            }

            if (row != size - 1) {
                System.out.print("\\");
            }

            System.out.print(rightPadding); // Added for the right alignment
            if (row == size - 1) {
                System.out.println(ANSI_BLUE + " ║" + ANSI_RESET); // Right border
            } else {
                System.out.println(ANSI_BLUE + "║" + ANSI_RESET); // Right border
            }
        }
        System.out.println(ANSI_RED + "====================================================================" + ANSI_RESET);
    }


    /**
     * Retrieves the color of the cell at a given row and column
     * @param row Row of the cell
     * @param col Column of the cell
     * @return Color of the cell
     **/
    //@requires 0 <= row && row < SIZE;
    //@requires 0 <= col && col < SIZE;
    //@ensures \result == board[row][col];
    public Color getFieldColor(int row, int col) {

        if (row < 0 || row >= SIZE || col < 0 || col >= SIZE) {
            throw new IllegalArgumentException("Coordinates out of bounds");
        }
        return board[row][col];
    }

    /**
     * Sets a cell to a specified color
     * @param row Row of the cell
     * @param col Column of the cell
     * @param color Color to set the cell to
     **/
    //@requires 0 <= row && row < SIZE;
    //@requires 0 <= col && col < SIZE;
    //@ensures board[row][col] == color;
    public void setField(int row, int col, Color color) {

        if (row < 0 || row >= SIZE || col < 0 || col >= SIZE) {
            throw new IllegalArgumentException("Coordinates out of bounds");
        }
        board[row][col] = color;
    }

    /**
     * Checks if a cell is empty
     * @param row Row of the cell
     * @param col Column of the cell
     * @return true if cell is empty, false otherwise
     **/
    //@requires 0 <= row && row < SIZE;
    //@requires 0 <= col && col < SIZE;
    //@ensures \result == (board[row][col] == Color.EMPTY);
    public boolean isFieldEmpty(int row, int col) {
        return getFieldColor(row, col) == Color.EMPTY;
    }

    /**
     * Checks if the entire board is full
     * @return true if the board is full, false otherwise
     **/
    //@ensures \result == (\forall int i; 0 <= i && i < SIZE; (\forall int j; 0 <= j && j < SIZE; board[i][j] != Color.EMPTY));
    //@pure;
    public boolean isBoardFull() {
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                if (board[row][col] == Color.EMPTY) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Checks if the entire board is empty
     * @return true if the board is empty, false otherwise
     **/
    //@ensures \result == (\forall int i; 0 <= i && i < SIZE; (\forall int j; 0 <= j && j < SIZE; board[i][j] == Color.EMPTY));
    //@pure;
    public boolean isBoardEmpty() {
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                if (board[row][col] != Color.EMPTY) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Swap a colored field and move it parallel to the main diagonal.
     * @param row Row of the colored field.
     * @param col Column of the colored field.
     */
    public void swapField(int row, int col) {
        // Validate that the field contains a RED piece
        if (getFieldColor(row, col) != Color.RED) {
            throw new IllegalArgumentException("Can only swap a RED colored field.");
        }

        // Set the current position to EMPTY
        setField(row, col, Color.EMPTY);

        // Directly swap row and col values
        setField(col, row, Color.BLUE);
    }

    /**
     * Returns a deep copy of the current board.
     * @return a deep copy of the current board
     */
    //@ensures \result != this;
    //@ensures (\forall int i; (i >= 0 && i < SIZE*SIZE); \result.board[i] == this.board[i]);
    public Board deepCopy() {
        Board deepCopy = new Board();
        for (int i = 0; i < SIZE; i++) {
            for (int j = 0; j < SIZE; j++) {
                deepCopy.setField(i, j, this.getFieldColor(i, j));
            }
        }
        return deepCopy;
    }
}
