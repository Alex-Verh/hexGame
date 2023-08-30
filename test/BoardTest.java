import client.model.Board;
import client.model.Color;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 *  Tests correct initialization of the board as well as evaluating board’s completion or other different scenarios.
 */
class BoardTest {

    private Board board;

    /**
     * Sets up the board before each test.
     */
    @BeforeEach
    void setUp() {
        board = new Board();
    }


    /**
     * Tests that all fields are empty when creating a new board
     */
    @Test
    void testFieldIsEmpty() {
        assertTrue(board.isFieldEmpty(0, 0));
        board.setField(0, 0, Color.RED);
        assertFalse(board.isFieldEmpty(0, 0));
    }

    /**
     * Tests if new copy is not same board and has same colors on certain places
     */
    @Test
    void testDeepCopy() {
        board.setField(0, 0,Color.RED);
        Board deepCopy = board.deepCopy();
        assertNotSame(board, deepCopy);
        assertEquals(board.getFieldColor(0, 0), deepCopy.getFieldColor(0, 0));
    }

    /**
     * Tests that the mark of a field can be set correctly
     */
    @Test
    void testSetField() {
        board.setField(0, 0, Color.RED);
        assertEquals(Color.RED, board.getFieldColor(0, 0));
        board.setField(1, 1, Color.BLUE);
        assertEquals(Color.BLUE, board.getFieldColor(1, 1));
    }

    /**
     * Tests if the board is full after completely filling it
     */
    @Test
    void testIsFull() {
        assertFalse(board.isBoardFull());
        for (int i = 0; i < Board.SIZE; i++) {
            for (int j = 0; j < Board.SIZE; j++) {
                board.setField(i, j, Color.RED);
            }
        }
        assertTrue(board.isBoardFull());
    }

    /**
     * Tests that the swap rule works correctly
     */
    @Test
    void testSwapRule() {


        // 1. Swap a RED field and verify it works correctly
        board.setField(2, 3, Color.RED); // Setting a sample field to RED

        board.swapField(2, 3);

        assertEquals(Color.EMPTY, board.getFieldColor(2, 3), "Original field should be EMPTY after swapping");
        assertEquals(Color.BLUE, board.getFieldColor(3, 2), "Swapped field should be set to BLUE");

        // 2. Attempt to swap a non-RED field and check for IllegalArgumentException
        board.setField(4, 5, Color.BLUE); // Setting a sample field to BLUE

        assertThrows(IllegalArgumentException.class, () -> {
            board.swapField(4, 5);
        }, "Swapping a non-RED field should throw IllegalArgumentException");

        // 3. Check RED field is EMPTY after swap and the swapped field is BLUE
        board.setField(6, 7, Color.RED); // Setting another sample field to RED

        board.swapField(6, 7);

        assertEquals(Color.EMPTY, board.getFieldColor(6, 7), "Original field should be EMPTY after swapping");
        assertEquals(Color.BLUE, board.getFieldColor(7, 6), "Swapped field should be set to BLUE");
    }

}