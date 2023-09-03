import client.controller.Protocol;
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
        ServerSocket serverSocket = new ServerSocket(0);
        Socket socket = new Socket("localhost", serverSocket.getLocalPort());
        Socket clientsocket = serverSocket.accept();

        BufferedReader serverReceiver = new BufferedReader(new InputStreamReader(clientsocket.getInputStream()));

        PipedWriter pipedWriter = new PipedWriter();
        PipedReader pipedReader = new PipedReader(pipedWriter);

        BufferedWriter bufferedWriter = new BufferedWriter(pipedWriter);
        BufferedReader bufferedReader = new BufferedReader(pipedReader);

        Protocol protocol = new Protocol(socket);
        ClientTUI multiPlayerTUI = new ClientTUI
                (bufferedReader, bufferedReader, protocol, "name", "AI");
        Thread thread = new Thread(multiPlayerTUI);
        thread.start();

        Thread.sleep(1000);

        assertTrue(multiPlayerTUI.isWaiting());
        Thread.sleep(1000);

        String message = serverReceiver.readLine();
        assertEquals("QUEUE", message);

        Thread.sleep(1000);

        bufferedWriter.write("NEWGAME~name~name2" + "\n");
        bufferedWriter.flush();

        Thread.sleep(1000);

        // the piped writer sends gameover to the game
        bufferedWriter.write("GAMEOVER" + "\n");
        bufferedWriter.flush();

        thread.join();
        // check if the thread is dead
        assertFalse(thread.isAlive());

        clientsocket.close();
    }
}

