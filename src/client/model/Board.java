package client.model;

public class Board {
    public static final int SIZE = 9;
    //@public invariant SIZE > 0;


    /* ANSI Color codes for console display */
    private static final String ANSI_RESET = "\u001B[0m";
    private static final String ANSI_BLUE = "\u001B[34m";
    private static final String ANSI_GREEN = "\u001B[38;5;34m";
    private static final String ANSI_RED = "\u001B[38;5;88m";

    private static Color[][] board;
    //@private invariant board != null;
    //@private invariant board.length == SIZE;
    //@private invariant (\forall int i; 0 <= i && i < SIZE; board[i].length == SIZE);

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
    public void printBoard() {
        // Top border with "-"
        System.out.println("  " + new String(new char[(SIZE + 2) * 3]).replace("\0", "-"));

        // Top margin filled with RED
        System.out.print("|    ");
        for (int i = 0; i < SIZE; i++) {
            System.out.print(ANSI_RED + "RR " + ANSI_RESET);
        }
        System.out.println("   |");

        for (int i = 0; i < SIZE; i++) {
            System.out.print("| " + ANSI_BLUE + "BB " + ANSI_RESET);  // Left margin
            for (int j = 0; j < SIZE; j++) {
                switch (board[i][j]) {
                    case RED:
                        System.out.print(ANSI_RED + "RR " + ANSI_RESET);
                        break;
                    case BLUE:
                        System.out.print(ANSI_BLUE + "BB " + ANSI_RESET);
                        break;
                    default:
                        System.out.print(ANSI_GREEN + String.format("%02d ", i * SIZE + j) + ANSI_RESET);
                        break;
                }
            }
            System.out.println(ANSI_BLUE + "BB " + ANSI_RESET + "|");  // Right margin
        }

        // Bottom margin filled with RED
        System.out.print("|    ");
        for (int i = 0; i < SIZE; i++) {
            System.out.print(ANSI_RED + "RR " + ANSI_RESET);
        }
        System.out.println("   |");

        // Bottom border with "-"
        System.out.println("  " + new String(new char[(SIZE + 2) * 3]).replace("\0", "-"));
    }

    /**
     * Retrieves the color of the cell at a given row and column
     * @param row Row of the cell
     * @param col Column of the cell
     * @return Color of the cell
     **/
    //@requires 1 <= row && row <= SIZE;
    //@requires 1 <= col && col <= SIZE;
    //@ensures \result == board[row-1][col-1];
    public Color getFieldColor(int row, int col) {
        row--;
        col--;

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
    //@requires 1 <= row && row <= SIZE;
    //@requires 1 <= col && col <= SIZE;
    //@ensures board[row-1][col-1] == color;
    public static void setField(int row, int col, Color color) {
        row--;
        col--;

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
    //@requires 1 <= row && row <= SIZE;
    //@requires 1 <= col && col <= SIZE;
    //@ensures \result == (board[row-1][col-1] == Color.EMPTY);
    public boolean isFieldEmpty(int row, int col) {
        return getFieldColor(row, col) == Color.EMPTY;
    }

    /**
     * Checks if the entire board is full
     * @return true if the board is full, false otherwise
     **/
    //@ensures \result == (\forall int i; 0 <= i && i < SIZE; (\forall int j; 0 <= j && j < SIZE; board[i][j] != Color.EMPTY));
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

    //TODO: remove on deployment
    public static void main(String[] args) {
        Board board = new Board();
        board.printBoard();
    }
}
