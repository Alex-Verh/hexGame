import client.controller.AIPlayer;
import client.model.*;
import org.junit.jupiter.api.Test;
import server.controller.Server;

import java.io.*;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ServerTest {

    /**
     * Tests if the server can handle multiple clients and multiple games
     */
    @Test
    void testPlayGame() throws IOException {
        Server server = new Server(1);
        server.start();
        System.out.println("Connecting to server...");
        Socket socket = new Socket("localhost", 1);
        Socket socket2 = new Socket("localhost", 1);

        BufferedReader reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        BufferedReader reader2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));

        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        BufferedWriter writer2 = new BufferedWriter(new OutputStreamWriter(socket2.getOutputStream()));

        System.out.println("Sending HELLO to server...");
        //Send Hello to server
        writer.write("HELLO~name1");
        writer.newLine();
        writer.flush();

        writer2.write("HELLO~name2~");
        writer2.newLine();
        writer2.flush();

        System.out.println("Reading HELLO from server...");
        //Read Hello from server
        String response = reader.readLine();
        String response2 = reader2.readLine();
        assertEquals("HELLO~AlexServer~CHAT~RANK", response);
        assertEquals("HELLO~AlexServer~CHAT~RANK", response2);

        //Send Login to server
        writer.write("LOGIN~name1");
        writer.newLine();
        writer.flush();

        writer2.write("LOGIN~name2");
        writer2.newLine();
        writer2.flush();

        //Read Login from server
        response = reader.readLine();
        response2 = reader2.readLine();
        assertEquals("LOGIN", response);
        assertEquals("LOGIN", response2);

        int i = 0;
        while (i < 1) {
            //Send QUEUE to server
            writer.write("QUEUE");
            writer.newLine();
            writer.flush();

            writer2.write("QUEUE");
            writer2.newLine();
            writer2.flush();

            //Read NEWGAME from server
            response = reader.readLine();
            response2 = reader2.readLine();


            String name1;
            String name2;

            BufferedWriter playerWriter1;
            BufferedWriter playerWriter2;
            if (response.equals("NEWGAME~name1~name2")) {
                assertEquals("NEWGAME~name1~name2", response);
                assertEquals("NEWGAME~name1~name2", response2);
                name1 = "name1";
                name2 = "name2";
                playerWriter1 = writer;
                playerWriter2 = writer2;
            } else {
                assertEquals("NEWGAME~name2~name1", response);
                assertEquals("NEWGAME~name2~name1", response2);
                name1 = "name1";
                name2 = "name2";
                playerWriter1 = writer2;
                playerWriter2 = writer;
            }

            Board board = new Board();
            Player player1 = new AIPlayer(Color.RED, board, name1, reader);
            Player player2 = new AIPlayer(Color.BLUE, board, name2, reader2);
            player1.setOpponent(player2);
            player2.setOpponent(player1);
            Game game = new Game(board, player1, player2);


            while (!game.isFinished()) {
                Move move = game.getValidMoves().get((int) Math.round(Math.random() * (game.getValidMoves().size() - 1)));
                playerWriter1.write("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()));
                playerWriter1.newLine();
                playerWriter1.flush();

                response = reader.readLine();
                response2 = reader2.readLine();
                assertEquals("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()), response);
                assertEquals("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()), response2);
                game.makeMove(move);

                if (game.isFinished()) {
                    break;
                }

                move = game.getValidMoves().get((int) Math.round(Math.random() * (game.getValidMoves().size() - 1)));
                playerWriter2.write("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()));
                playerWriter2.newLine();
                playerWriter2.flush();

                response = reader.readLine();
                response2 = reader2.readLine();
                assertEquals("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()), response);
                assertEquals("MOVE~" + (move.getRow() * Board.SIZE + move.getCol()), response2);
                game.makeMove(move);

            }

            response = reader.readLine();
            response2 = reader2.readLine();

            assertEquals("GAMEOVER~VICTORY~" + ((AbstractPlayer) game.getWinner()).getName(), response);
            assertEquals("GAMEOVER~VICTORY~" + ((AbstractPlayer) game.getWinner()).getName(), response2);

            assertTrue(game.isFinished());
            i++;
        }

        socket.close();
        socket2.close();

    }

}
