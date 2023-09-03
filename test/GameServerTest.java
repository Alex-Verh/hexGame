import client.model.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import server.controller.ClientHandler;
import server.controller.Protocol;
import server.controller.Server;
import server.model.GameServer;

import java.io.BufferedWriter;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class GameServerTest {


    private Server server;
    private ClientHandler player1;
    private ClientHandler player2;
    private GameServer game;
    private Board board;

    @BeforeEach
    public void setup() throws IOException {
        ServerSocket serverSocket = new ServerSocket(0);
        server = new Server(0);
        Socket socket = new Socket("localhost", serverSocket.getLocalPort());
        Socket socket2 = new Socket("localhost", serverSocket.getLocalPort());
        player1 = new ClientHandler(socket, server);
        player2 = new ClientHandler(socket2, server);
        game = new GameServer(player1, player2, server);
        board = game.getBoard();
    }


    @Test
    void testGetBoard() {
        assertEquals(board, game.getBoard());
    }

    @Test
    void testCountFields() {
        game.makeMove(new Move(0, 0, Color.RED));
        game.makeMove(new Move(1, 1, Color.BLUE));
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
        Move move = new Move(0, 0,  Color.RED);
        assertTrue(game.isValidMove(move));
    }

    @Test
    void testMakeMove() {
        Move move = new Move(0, 0, Color.RED);
        game.makeMove(move);
        assertEquals(Color.RED, board.getFieldColor(0, 0));
    }

    /**
     * Tests if the game is over when board is empty and in case if it is full
     */
    @Test
    void testIsGameOver() {

        for (int i = 0; i < Board.SIZE; i++) {
            for (int j = 0; j < Board.SIZE; j++) {
                if (board.isFieldEmpty(i, j)) {
                    game.makeMove(new Move(i, j, Color.RED));
                }
            }
        }

        assertTrue(game.isFinished());

        game = new GameServer(player1, player2, server);

        for (int row = 0; row < Board.SIZE; row++) {
            game.getBoard().setField(row, 0, Color.BLUE);
            game.getBoard().setField(row, 1, Color.BLUE);
            game.getBoard().setField(row, 2, Color.BLUE);
            game.getBoard().setField(row, 3, Color.BLUE);
            game.getBoard().setField(row, 4, Color.BLUE);
            game.getBoard().setField(row, 5, Color.BLUE);
            game.getBoard().setField(row, 6, Color.BLUE);
            game.getBoard().setField(row, 7, Color.BLUE);
            game.getBoard().setField(row, 8, Color.BLUE);
        }
        assertTrue(game.isFinished());
    }

    /**
     * Tests if there is a winner when board is empty and in case it is full
     */
    @Test
    void testGetWinner() {
        assertNull(game.getWinner());

        for (int i = 0; i < Board.SIZE; i++) {
            for (int j = 0; j < Board.SIZE; j++) {
                if (board.isFieldEmpty(i, j)) {
                    game.makeMove(new Move(i, j, Color.RED));
                }
            }
        }

        assertEquals(game.getWinner(), player2.getClientName());
        game.getBoard().displayBoard();
        System.out.println(game.getWinner());
        game = new GameServer(player1, player2, server);

        game.getBoard().setField(1, 0, Color.BLUE);
        game.getBoard().setField(1, 1, Color.BLUE);
        game.getBoard().setField(1, 2, Color.BLUE);
        game.getBoard().setField(1, 3, Color.BLUE);
        game.getBoard().setField(1, 4, Color.BLUE);
        game.getBoard().setField(1, 5, Color.BLUE);
        game.getBoard().setField(1, 6, Color.BLUE);
        game.getBoard().setField(1, 7, Color.BLUE);
        game.getBoard().setField(1, 8, Color.BLUE);


        assertEquals(game.getWinner(), player1.getClientName());
    }

    /**
     * Checking move functionality and correct functioning of doMove method
     */
    @Test
    void testDoMove() {

        Move move = new Move(0, 0, Color.BLUE);
        game.makeMove(move);

        assertEquals(Color.BLUE, board.getFieldColor(0, 0));


        move = new Move(2, 3,Color.RED);
        game.makeMove(move);
        assertEquals(Color.RED, board.getFieldColor(2, 3));
    }

    /**
     * Tests overall functionality during a randomly simulated game;
     */
    @Test
    void testRandomGame() {
        while (!game.isFinished()) {
            // get the valid moves for the current player
            List<Move> validMoves = game.getValidMoves();

            // choose a random move from the list of valid moves
            int moveIndex = (int) (Math.random() * validMoves.size());
            Move move = validMoves.get(moveIndex);

            // check that the move is valid
            assertTrue(game.isValidMove(move));

            // make the move
            game.makeMove(move);
            // get the valid moves for the current player
            validMoves = game.getValidMoves();

            if (game.isFinished()) {
                break;
            }

            // choose a random move from the list of valid moves
            moveIndex = (int) (Math.random() * validMoves.size());
            move = validMoves.get(moveIndex);

            // check that the move is valid
            assertTrue(game.isValidMove(move));

            // make the move
            game.makeMove(move);
        }
        // check that the game is over
        assertTrue(game.isFinished());
    }

}

