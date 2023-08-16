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
     * Gets player that has to move at the moment.
     * @return currentPlayer that has to move
     */
    //@ensures \result == player1 || \result == player2;
    //@pure;
    public Player getCurrentPlayer() {
        return currentPlayer;
    }

    /**
     * Switch to the next player.
     */
    private void switchCurrentPlayer() {
        currentPlayer = (currentPlayer == player1) ? player2 : player1;
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
                    validMoves.add(new Move(row + 1, col + 1, currentPlayer.getColor()));
                }
            }
        }
    }

    /**
     * Make a move on the board.
     *
     * @param move The move to be made.
     */
    public void makeMove(Move move) {
        // Check if move is valid
        if (move != null && getValidMoves().contains(move)) {
            List<Integer> counts = countFields();
            int redFields = counts.get(0);
            int blueFields = counts.get(1);

            // Check if the move is a special swap move
            if (move.getRow() == -1 && move.getCol() == -1 && move.getColor() == Color.BLUE) {
                // Get the position of the RED piece on the board (assuming there's only one, since it's the second move)
                for (int i = 1; i <= Board.SIZE; i++) {
                    for (int j = 1; j <= Board.SIZE; j++) {
                        if (board.getFieldColor(i, j) == Color.RED) {
                            board.swapField(i, j);
                            switchCurrentPlayer();
                            return;
                        }
                    }
                }
                System.out.println("No RED piece to be swapped!");
            }

            // Place the player's color on the board
            board.setField(move.getRow(), move.getCol(), move.getColor());
            switchCurrentPlayer();
        } else {
            System.out.println("Illegal Move.");
        }
    }

    /**
     * Checks if game is finished.
     * @return true || false if game is over or not
     */
    //@ensures getBoard().isBoardFull() || getValidMoves().isEmpty();
    //@pure;
    public boolean isFinished() {
        return board.isBoardFull() || getValidMoves().isEmpty() || (getWinner() == player1 || getWinner() == player2);
    }

    /**
     * Gets the winner of the game, decided by a connection of hexagons between vertical and horizontal lines.
     * Uses Depth First Search (DFS) to determine if a player has a winning path from one side of the board to the other.
     *
     * @return the winning player if one exists, null otherwise
     */
    //@ ensures \result == player1 || \result == player2 || \result == null;
    //@ pure;
    public Player getWinner() {
        // Check for a winning path for Player 1 (assume they connect top to bottom)
        for (int col = 1; col <= Board.SIZE; col++) {
            if (board.getFieldColor(1, col) == player1.getColor()) {
                if (dfs(1, col, player1.getColor(), new boolean[Board.SIZE][Board.SIZE])) {
                    return player1;
                }
            }
        }

        // Check for a winning path for Player 2 (assume they connect left to right)
        for (int row = 1; row <= Board.SIZE; row++) {
            if (board.getFieldColor(row, 1) == player2.getColor()) {
                if (dfs(row, 1, player2.getColor(), new boolean[Board.SIZE][Board.SIZE])) {
                    return player2;
                }
            }
        }

        return null;
    }

    /**
     * Depth First Search (DFS) to check if the specified color has a winning path on the board.
     * The DFS starts from the given row and col and explores possible paths in depth to check if the player with the specified color has a winning path.
     *
     * @param row The starting row of the DFS.
     * @param col The starting column of the DFS.
     * @param color The color for which we are checking the path.
     * @param visited A 2D boolean array that keeps track of which board positions have already been visited in this DFS.
     * @return true if the color has a winning path starting from the given row and col, false otherwise.
     */
    //@ requires 0 <= row && row < Board.SIZE && 0 <= col && col < Board.SIZE;
    //@ requires color != null && color != Color.EMPTY;
    //@ requires visited != null && visited.length == Board.SIZE && (\forall int i; 0 <= i && i < Board.SIZE; visited[i].length == Board.SIZE);
    //@ ensures \result == true || \result == false;
    //@ pure;
    private boolean dfs(int row, int col, Color color, boolean[][] visited) {
        if (row < 1 || col < 1 || row > Board.SIZE || col > Board.SIZE) {
            return false;
        }

        if (board.getFieldColor(row, col) != color || visited[row-1][col-1]) {
            return false;
        }

        if ((color == player1.getColor() && row == Board.SIZE) || (color == player2.getColor() && col == Board.SIZE)) {
            return true;
        }

        visited[row-1][col-1] = true;

        int[][] directions = {
                {-1, 0}, {1, 0}, {0, -1}, {0, 1}, {-1, 1}, {1, -1}
        };

        for (int[] direction : directions) {
            int newRow = row + direction[0];
            int newCol = col + direction[1];

            if (dfs(newRow, newCol, color, visited)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Returns a copy of the game.
     * @return the copy of the game
     */
    //@ensures \result != this;
    /*@requires !this.getBoard().isBoardFull() && this.getBoard() != null &&
        this.player1.getColor() != Color.EMPTY && this.player1.getOpponent() != null &&
            this.player1 != null && this.player2.getColor() != Color.EMPTY &&
                this.player2.getOpponent() != null && this.player2 != null; */
    public Game deepCopy() {
        Board newBoard = board.deepCopy();
        Player newPlayer1 = player1.deepCopy();
        Player newPlayer2 = player2.deepCopy();
        Game copyGame = new Game(newBoard, newPlayer1, newPlayer2);
        copyGame.currentPlayer = currentPlayer;
        return copyGame;
    }

//    public static void main(String[] args) {
//        // Step 1: Create a board and two player objects.
//        Board board = new Board();
//        Player player1 = new AbstractPlayer(Color.RED, board, "Player1");
//        Player player2 = new AbstractPlayer(Color.BLUE, board, "Player2");
//        player1.setOpponent(player2);
//        player2.setOpponent(player1);
//
//        // Step 2: Instantiate the game.
//        Game game = new Game(board, player1, player2);
//
//        // Step 3: Simulate some moves.
//
//        // Player 1 moves
//        game.makeMove(new Move(1, 1, player1.getColor()));  // Top-left corner
//        game.makeMove(new Move(1, 2, player2.getColor()));  // Top, one step to the right
//
//        game.makeMove(new Move(2, 1, player1.getColor()));  // One step diagonally
//        game.makeMove(new Move(2, 2, player2.getColor()));  // Left, one step down
//
//        game.makeMove(new Move(3, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(3, 2, player2.getColor()));  // Left, one step down
//        game.makeMove(new Move(4, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(4, 2, player2.getColor()));  // Another diagonal
//        game.makeMove(new Move(5, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(5, 2, player2.getColor()));  // Another diagonal
//        game.makeMove(new Move(6, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(6, 2, player2.getColor()));  // Another diagonal        game.makeMove(new Move(5, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(7, 1, player1.getColor()));  // Another diagonal        game.makeMove(new Move(5, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(7, 2, player2.getColor()));  // Another diagonal
//        game.makeMove(new Move(8, 1, player1.getColor()));  // Another diagonal        game.makeMove(new Move(5, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(8, 2, player2.getColor()));
//        game.makeMove(new Move(9, 3, player1.getColor()));  // Another diagonal        game.makeMove(new Move(5, 1, player1.getColor()));  // Another diagonal
//        game.makeMove(new Move(9, 2, player2.getColor()));
//
//        // Player 2 moves
//
//        // More moves can be added here for further testing
//
//        // Check the winner
//        AbstractPlayer winner = (AbstractPlayer) game.getWinner();
//        if (winner != null) {
//            System.out.println(winner.getName() + " is the winner!");
//        } else {
//            System.out.println("No winner yet.");
//        }
//
//        // Check if the game is finished
//        if (game.isFinished()) {
//            System.out.println("The game is over.");
//        } else {
//            System.out.println("The game is still ongoing.");
//        }
//
//        // You can also print the board state here to visualize it
//        board.displayBoard();
//    }
}