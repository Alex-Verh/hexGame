import client.controller.NetworkPlayer;
import client.controller.Protocol;
import client.controller.RealPlayer;
import client.model.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

/**
 *  Tests creation of a NetworkPlayer object from the NetworkPlayer class that is responsible for reading moves from the server to the Listener class.
 */
class NetworkPlayerTest {
    private Player opponent1;
    private Player opponent2;
    private Board board;

    @BeforeEach
    public void setup() {
        board = new Board();
        opponent1 = new NetworkPlayer(Color.RED, board, "player1",null);
        opponent2 = new NetworkPlayer(Color.BLUE, board, "player2",null);
    }

    /**
     * Tests methods setOpponent and getOpponent
     */
    @Test
    void testSetGetOpponent() {
        assertNull(opponent1.getOpponent());

        opponent1.setOpponent(opponent2);
        assertEquals(opponent2, opponent1.getOpponent());
        assertNull(opponent2.getOpponent());

        opponent2.setOpponent(opponent1);
        assertEquals(opponent2, opponent1.getOpponent());
        assertEquals(opponent1, opponent2.getOpponent());
    }

    /**
     * Tests methods getColor functionality
     */
    @Test
    void testGetColor() {
        assertEquals(Color.RED, opponent1.getColor());
        assertEquals(Color.BLUE, opponent2.getColor());

        Player opponent3 = new RealPlayer(Color.EMPTY, board, "player3", null, null);

        assertEquals(Color.EMPTY, opponent3.getColor());
    }

    /**
     * Tests deepCopy method
     */
    @Test
    void testDeepCopy() {
        opponent1.setOpponent(opponent2);
        Player opponent3 = opponent1.deepCopy();
        assertNotEquals(opponent1, opponent3);
        assertEquals(opponent1.getOpponent(), opponent3.getOpponent());
        assertEquals(opponent1.getColor(), opponent3.getColor());
        assertEquals(opponent1.getBoard(), opponent3.getBoard());

    }

    /**
     * Tests getName method
     */
    @Test
    void testToString() {
        assertEquals("player1", ((AbstractPlayer) opponent1).getName());
        assertEquals("player2", ((AbstractPlayer) opponent2).getName());
    }

    /**
     * Tests if move works correctly in different situations
     * @throws IOException when does not connect
     */
    @Test
    void testMove() throws IOException {

        ServerSocket serverSocket = new ServerSocket(1234);
        Socket socket = new Socket("localhost", 1234);
        serverSocket.accept();

        Game game = new Game(board, opponent1, opponent2);
        Protocol protocol = new Protocol(socket);
        PipedWriter writer = new PipedWriter();
        PipedReader reader = new PipedReader(writer);
        BufferedReader bufferedReader = new BufferedReader(reader);
        NetworkPlayer opponent1 = new NetworkPlayer(Color.RED, board, "player", bufferedReader);
        NetworkPlayer opponent2 = new NetworkPlayer(Color.BLUE, board, "player2", bufferedReader);

        writer.write("GAMEOVER" + "\n");
        writer.flush();


        Move move = opponent1.move(game, protocol);
        assertNull(move);

        writer.write("MOVE~32" + "\n");
        writer.flush();
        move = opponent2.move(game, protocol);
        assertEquals(new Move(3, 5, opponent2.getColor()), move);

    }

}