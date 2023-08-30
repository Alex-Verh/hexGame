import client.model.Board;
import client.model.Color;
import client.model.Move;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class MoveTest {

    @Test
    void testConstructorAndGetters() {
        Move move = new Move(5, 4, Color.RED);

        assertEquals(5, move.getRow(), "Row mismatch");
        assertEquals(4, move.getCol(), "Column mismatch");
        assertEquals(Color.RED, move.getColor(), "Color mismatch");
    }

    @Test
    void testToString() {
        Move move = new Move(5, 4, Color.RED);
        int expectedHashCode = 5 * Board.SIZE + 4;
        String expectedString = String.format("Move {Index: %d, Row: 5, Col: 4, Mark: RED}", expectedHashCode);

        assertEquals(expectedString, move.toString(), "toString output mismatch");
    }

    @Test
    void testHashCode() {
        Move move = new Move(5, 4, Color.RED);
        int expectedHashCode = 5 * Board.SIZE + 4;

        assertEquals(expectedHashCode, move.hashCode(), "Hashcode mismatch");
    }

    @Test
    void testEquals() {
        Move move1 = new Move(5, 4, Color.RED);
        Move move2 = new Move(5, 4, Color.RED);
        Move move3 = new Move(6, 4, Color.RED);
        Move move4 = new Move(5, 4, Color.BLUE);

        assertEquals(move1, move2, "Both moves should be equal");
        assertNotEquals(move1, move3, "Moves with different rows should not be equal");
        assertNotEquals(move1, move4, "Moves with different colors should not be equal");
        assertNotEquals(null, move1, "Move should not be equal to null");
        assertNotEquals(move1, new Object(), "Move should not be equal to a different object type");
    }

    @Test
    void testInvalidMove() {
        assertThrows(IllegalArgumentException.class, () -> new Move(-1, 4, Color.RED), "Row out of range");
        assertThrows(IllegalArgumentException.class, () -> new Move(5, -1, Color.RED), "Column out of range");
        assertThrows(IllegalArgumentException.class, () -> new Move(5, 4, null), "Color is null");
    }
}
