import client.model.AbstractPlayer;
import client.model.Board;
import client.model.Color;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the AbstractPlayer class.
 */
public class AbstractPlayerTest {
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private Board board;

    /**
     * Set up the test environment with players and board.
     */
    @BeforeEach
    void setUp() {
        board = new Board();
        player1 = new AbstractPlayer(Color.RED, board, "name1");
        player2 = new AbstractPlayer(Color.BLUE, board, "name2");
    }

    /**
     * Test the constructor of AbstractPlayer.
     */
    @Test
    public void testConstructor() {
        assertEquals(Color.RED, player1.getColor());
        assertEquals(board, player1.getBoard());
        assertEquals("name1", player1.getName());

        assertEquals(Color.BLUE, player2.getColor());
        assertEquals(board, player2.getBoard());
        assertEquals("name2", player2.getName());
    }

    /**
     * Test getColor() method to ensure it returns the correct color for each player.
     */
    @Test
    public void testGetColor() {
        assertEquals(Color.RED, player1.getColor());
        assertEquals(Color.BLUE, player2.getColor());
    }

    /**
     * Test setting and getting opponent players.
     */
    @Test
    public void testSetAndGetOpponent() {
        player1.setOpponent(player2);

        assertEquals(player2, player1.getOpponent());

        player2.setOpponent(player1);

        assertEquals(player1, player2.getOpponent());
    }

    /**
     * Test to ensure the getBoard() method returns the correct board for each player.
     */
    @Test
    public void testGetBoard() {
        assertEquals(board, player1.getBoard());
        assertEquals(board, player2.getBoard());

    }

    /**
     * Test to ensure deepCopy() creates an accurate copy of a player.
     */
    @Test
    public void testDeepCopy() {
        AbstractPlayer copiedPlayer = (AbstractPlayer) player1.deepCopy();

        assertEquals(player1.getColor(), copiedPlayer.getColor());
        assertEquals(player1.getName(), copiedPlayer.getName());
        assertEquals(player1.getBoard(), copiedPlayer.getBoard());

        AbstractPlayer copiedPlayer2 = (AbstractPlayer) player2.deepCopy();

        assertEquals(player2.getColor(), copiedPlayer2.getColor());
        assertEquals(player2.getName(), copiedPlayer2.getName());
        assertEquals(player2.getBoard(), copiedPlayer2.getBoard());
    }

    /**
     * Test to ensure getName() returns the correct player name.
     */
    @Test
    public void testGetName() {
        assertEquals("name1", player1.getName());
        assertEquals("name2", player2.getName());
    }
}
