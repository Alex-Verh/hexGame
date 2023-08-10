package client.model;

public class Board {
    private static final int SIZE = 9;
    private static final String ANSI_RESET = "\u001B[0m";
    private static final String ANSI_BLUE = "\u001B[34m";
    private static final String ANSI_GREEN = "\u001B[38;5;34m";
    private static final String ANSI_RED = "\u001B[38;5;88m";

    private static Color[][] board;

    public Board() {
        board = new Color[SIZE][SIZE];
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                board[row][col] = Color.EMPTY;
            }
        }
    }

    enum Color {
        EMPTY, RED, BLUE;
    }

    public void printBoard() {
        // Top margin
        System.out.println("  " + new String(new char[SIZE * 3]).replace("\0", "-"));

        for (int i = 0; i < SIZE; i++) {
            System.out.print("| ");  // Left margin
            for (int j = 0; j < SIZE; j++) {
                switch (board[i][j]) {
                    case RED:
                        System.out.print(ANSI_RED + "\uD83C\uDF53 " + ANSI_RESET);
                        break;
                    case BLUE:
                        System.out.print(ANSI_BLUE + "\uD83C\uDF46 " + ANSI_RESET);
                        break;
                    default:
                        System.out.print(ANSI_GREEN + String.format("%02d ", i * SIZE + j) + ANSI_RESET);
                        break;
                }
            }
            System.out.println("|");  // Right margin
        }

        // Bottom margin
        System.out.println("  " + new String(new char[SIZE * 3]).replace("\0", "-"));
    }

    public Color getFieldColor(int row, int col) {
        row--;
        col--;

        if (row < 0 || row >= SIZE || col < 0 || col >= SIZE) {
            throw new IllegalArgumentException("Coordinates out of bounds");
        }
        return board[row][col];
    }

    public static void setField(int row, int col, Color color) {
        row--;
        col--;

        if (row < 0 || row >= SIZE || col < 0 || col >= SIZE) {
            throw new IllegalArgumentException("Coordinates out of bounds");
        }
        board[row][col] = color;
    }

    public boolean isFieldEmpty(int row, int col) {
        return getFieldColor(row, col) == Color.EMPTY;
    }

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

    public static void main(String[] args) {
        Board board = new Board();
        board.printBoard();
        setField(2,2, Color.RED);
        setField(2,2, Color.RED);
        board.printBoard();
        setField(2,3, Color.BLUE);
        board.printBoard();

    }
}
