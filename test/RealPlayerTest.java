
import client.controller.Protocol;
import client.controller.RealPlayer;
import client.model.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import server.controller.Server;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

 class RealPlayerTest {

    private RealPlayer player;
    private Game game;
    private Protocol protocol;

     @BeforeEach
    public void setUp() throws IOException {

        ServerSocket serverSocket = new ServerSocket(0);
        Server server = new Server(serverSocket.getLocalPort());
        Socket socket = new Socket("localhost", serverSocket.getLocalPort());
        Socket clientSocket = serverSocket.accept();

        Board board = new Board(); // Assuming a constructor without parameters
         BufferedReader reader1 = new BufferedReader(new StringReader("suggest\n0")); // a dummy input
         BufferedReader reader2 = new BufferedReader(new StringReader("MOVE~5"));
        player = new RealPlayer(Color.RED, board, "testPlayer", reader1, reader2);
        RealPlayer player2 = new RealPlayer(Color.BLUE, board, "testPlayer2", reader1, reader2);

        // Assuming Game class has a constructor with Board and Player. This is an assumption.
        game = new Game(board, player, player2);
        protocol = new Protocol(clientSocket); // This assumes that Protocol has a default constructor.
    }

    @Test
    void testMove() {
        Move move = player.move(game, protocol);
        assertNotNull(move);
        assertEquals(Color.RED, move.getColor());
    }

    @Test
     void testSuggestMove() {
        Move move = player.suggestMove(game);
        assertNotNull(move);
        assertTrue(game.isValidMove(move));
    }

    @Test
    void testDeepCopy() {
        Player copiedPlayer = player.deepCopy();
        assertNotEquals(player, copiedPlayer);
    }
}

