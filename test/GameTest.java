import static org.junit.jupiter.api.Assertions.*;

import client.model.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

class GameTest {

    private Game game;
    // Assuming Board has a default constructor.
    private final Board board = new Board();
    private Player player1, player2;

    @BeforeEach
     void setUp() {
        player1 = new AbstractPlayer(Color.RED, board,"Player 1"); // Assuming Player has a constructor with name and color.
        player2 = new AbstractPlayer(Color.BLUE, board,"Player 2"); // Assuming Player has a constructor with name and color.
        game = new Game(board, player1, player2);
    }

    @Test
     void testGetBoard() {
        assertEquals(board, game.getBoard());
    }

    @Test
     void testGetCurrentPlayer() {
        assertEquals(player1, game.getCurrentPlayer());
        game.makeMove(new Move(0, 0, player1.getColor()));
        assertEquals(player2, game.getCurrentPlayer());
    }

    @Test
     void testSwitchCurrentPlayer() {
        game.makeMove(new Move(0, 0, player1.getColor()));
        assertEquals(player2, game.getCurrentPlayer());
    }

    @Test
     void testCountFields() {
        game.makeMove(new Move(0, 0, player1.getColor()));
        game.makeMove(new Move(1, 1, player2.getColor()));
        List<Integer> result = game.countFields();
        assertEquals(1, result.get(0)); // 1 RED
        assertEquals(1, result.get(1)); // 1 BLUE
    }

    @Test
     void testGetValidMoves() {
        List<Move> moves = game.getValidMoves();
        assertTrue(moves.size() > 0);
    }

    @Test
     void testIsValidMove() {
        Move move = new Move(0, 0, player1.getColor());
        assertTrue(game.isValidMove(move));
    }

    @Test
     void testMakeMove() {
        Move move = new Move(0, 0, player1.getColor());
        game.makeMove(move);
        assertEquals(Color.RED, board.getFieldColor(0, 0));
    }

    @Test
     void testIsFinished() {
        assertFalse(game.isFinished());
    }

    @Test
     void testGetWinner() {
        // Assume Board.SIZE = 5 for simplicity

        // No winner at the start
        assertNull(game.getWinner());

        // Player 1's winning path from top to bottom
        for (int col = 0; col < Board.SIZE; col++) {
            game.getBoard().setField(0, col, player1.getColor());
            game.getBoard().setField(1, col, player1.getColor());
            game.getBoard().setField(2, col, player1.getColor());
            game.getBoard().setField(3, col, player1.getColor());
            game.getBoard().setField(4, col, player1.getColor());
            game.getBoard().setField(5, col, player1.getColor());
            game.getBoard().setField(6, col, player1.getColor());
            game.getBoard().setField(7, col, player1.getColor());
            game.getBoard().setField(8, col, player1.getColor());
        }
        assertEquals(player1, game.getWinner());

        // Resetting the board
        for (int i = 0; i < Board.SIZE; i++) {
            for (int j = 0; j < Board.SIZE; j++) {
                game.getBoard().setField(i, j, Color.EMPTY);
            }
        }

        // Player 2's winning path from left to right
        for (int row = 0; row < Board.SIZE; row++) {
            game.getBoard().setField(row, 0, player2.getColor());
            game.getBoard().setField(row, 1, player2.getColor());
            game.getBoard().setField(row, 2, player2.getColor());
            game.getBoard().setField(row, 3, player2.getColor());
            game.getBoard().setField(row, 4, player2.getColor());
            game.getBoard().setField(row, 5, player2.getColor());
            game.getBoard().setField(row, 6, player2.getColor());
            game.getBoard().setField(row, 7, player2.getColor());
            game.getBoard().setField(row, 8, player2.getColor());

        }
        assertEquals(player2, game.getWinner());
    }

    @Test
     void testDeepCopy() {
        game.makeMove(new Move(0, 0, player1.getColor()));
        game.makeMove(new Move(1, 1, player2.getColor()));
        Game copiedGame = game.deepCopy();
        assertNotSame(game, copiedGame);
        assertEquals(((AbstractPlayer) game.getCurrentPlayer()).getName(), ((AbstractPlayer) copiedGame.getCurrentPlayer()).getName());
        // The games should not be the same object
        assertNotSame(game, copiedGame);
        assertNotSame(game.getBoard(), copiedGame.getBoard());
        // The states of the games should be the same
        assertEquals(game.getBoard().getFieldColor(0, 0), copiedGame.getBoard().getFieldColor(0, 0));
        assertEquals(game.getBoard().getFieldColor(1, 1), copiedGame.getBoard().getFieldColor(1, 1));
        // Changing the original game should not affect the copied game
        game.makeMove(new Move(2, 2, player1.getColor()));
        assertNotEquals(game.getBoard().getFieldColor(2, 2), copiedGame.getBoard().getFieldColor(2, 2));
    }
}
