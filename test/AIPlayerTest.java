import client.controller.AIPlayer;
import client.model.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class AIPlayerTest {
    private AIPlayer aiPlayer;
    private final Board board = new Board();
    private String name;

    /**
     * Tests if getting a mark of an AI works correctly
     */
    @Test
    void testGetMark() {
        aiPlayer = new AIPlayer(Color.RED, board, name, null);
        assertEquals(Color.RED, aiPlayer.getColor());
        assertNotEquals(Color.BLUE, aiPlayer.getColor());
        assertNotEquals(Color.EMPTY, aiPlayer.getColor());

        aiPlayer = new AIPlayer(Color.BLUE, board, name, null);
        assertEquals(Color.BLUE, aiPlayer.getColor());
        assertNotEquals(Color.RED, aiPlayer.getColor());
        assertNotEquals(Color.EMPTY, aiPlayer.getColor());
    }

    /**
     * Test the deepCopy method
     */
    @Test
    void testDeepCopy() {
        aiPlayer = new AIPlayer(Color.RED, board, name, null);
        Player player1 = new AIPlayer(Color.BLUE, board, name, null);
        aiPlayer.setOpponent(player1);
        Player aiPlayerCopy = aiPlayer.deepCopy();
        assertNotEquals(aiPlayer, aiPlayerCopy);
        assertEquals(aiPlayer.getColor(), aiPlayerCopy.getColor());
        assertEquals(aiPlayer.getName(), ((AIPlayer) aiPlayerCopy).getName());
        assertEquals(aiPlayer.getOpponent(), aiPlayerCopy.getOpponent());
        assertEquals(aiPlayer.getBoard(), aiPlayerCopy.getBoard());
    }

    /**
     * Tests getName method
     */
    @Test
    void testGetName() {
        name = "Name1";
        AIPlayer aiPlayer = new AIPlayer(Color.RED, board, name, null);
        name = "Name2";
        AIPlayer aiPlayerAnother = new AIPlayer(Color.BLUE, board, name, null);

        assertEquals("Name1", aiPlayer.getName());
        assertEquals("Name2", aiPlayerAnother.getName());

        assertEquals(aiPlayer.getName(), ((AIPlayer) aiPlayer.deepCopy()).getName());
        assertEquals(aiPlayerAnother.getName(), ((AIPlayer) aiPlayerAnother.deepCopy()).getName());
    }
}
