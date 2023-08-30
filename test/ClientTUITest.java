import client.controller.Protocol;
import client.model.Board;
import client.model.Game;
import client.view.ClientTUI;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

class ClientTUITest {
    @Test
     void testGetPlayerType() {
        BufferedReader clientInput = new BufferedReader(new StringReader("AI\n"));
        String playerType = ClientTUI.getPlayerType(clientInput);

        assertEquals("AI", playerType);
    }

    /**
     * Tests Client class functionality and verifies if isWaiting is working properly
     * @throws IOException if the socket is not connected
     * @throws InterruptedException if the thread is interrupted
     */
    @Test
    void testClient() throws IOException, InterruptedException {
        // Create a server socket and connect to it
        ServerSocket serverSocket = new ServerSocket(0);
        Socket socket = new Socket("localhost", serverSocket.getLocalPort());
        Socket clientsocket = serverSocket.accept();

        // Create a buffered reader to read from the server
        BufferedReader serverReceiver = new BufferedReader(new InputStreamReader(clientsocket.getInputStream()));

        // Create a buffered writer to write to the server
        PipedWriter pipedWriter = new PipedWriter();
        PipedReader pipedReader = new PipedReader(pipedWriter);

        // Create a buffered writer to write to the server
        BufferedWriter bufferedWriter = new BufferedWriter(pipedWriter);
        BufferedReader bufferedReader = new BufferedReader(pipedReader);

        // Create a protocol and a MultiPlayerTUI
        Protocol protocol = new Protocol(socket);
        ClientTUI multiPlayerTUI = new ClientTUI
                (bufferedReader, bufferedReader, protocol, "name", "AI");
        // Start the thread
        Thread thread = new Thread(multiPlayerTUI);
        thread.start();

        // Checks if the server receives the correct message
        String message = serverReceiver.readLine();
        assertEquals("QUEUE", message);

        // the piped writer sends newgame to the game
        bufferedWriter.write("NEWGAME~name~name2" + "\n");
        bufferedWriter.flush();

        Thread.sleep(1000);


        // the piped writer sends gameover to the game
        bufferedWriter.write("GAMEOVER" + "\n");
        bufferedWriter.flush();

        thread.join();
        // check if the thread is dead
        assertFalse(thread.isAlive());

    }
}

