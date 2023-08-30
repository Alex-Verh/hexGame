import org.junit.jupiter.api.Test;
import server.controller.ClientHandler;
import server.controller.Server;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

/**
 *  Tests correct functionality of the actual ClientHandler class that is responsible for handling commands from the client and forwarding them to the actual gameplay.
 */
class ClientHandlerTest {

    /**
     * Tests the correct functionality of the ClientHandler class so if the commands are correctly handled.
     * @throws IOException when the socket is not connected
     * @throws InterruptedException when the thread is interrupted
     */
    @Test
    void testClientHandler() throws IOException, InterruptedException {
        ServerSocket serverSocket = new ServerSocket(0);
        Server server = new Server(0);
        Socket socket = new Socket("localhost", serverSocket.getLocalPort());
        Socket clientSocket = serverSocket.accept();

        ClientHandler clientHandler = new ClientHandler(socket, server);
        Thread thread = new Thread(clientHandler);
        thread.start();
        BufferedWriter bufferedWriter = new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream()));
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
        bufferedWriter.write("HELLO~AlexClient~CHAT~RANK" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertTrue(clientHandler.getChat());

        String message = bufferedReader.readLine();
        assertEquals("HELLO~AlexServer~CHAT~RANK", message);

        bufferedWriter.write("alex" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertNull(clientHandler.getClientName()); // Since protocol is not correct yet

        message = bufferedReader.readLine();
        assertEquals("ERROR~Unknown command expected LOGIN~<username>", message);

        bufferedWriter.write("LOGIN~alex" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertEquals("alex", clientHandler.getClientName());

        message = bufferedReader.readLine();
        assertEquals("LOGIN", message);

        assertTrue(server.getAllUsers().contains("alex"));

        bufferedWriter.write("LIST" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertEquals("LIST~alex", bufferedReader.readLine());

        bufferedWriter.write("CHALLENGE~alex" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertEquals("ERROR~Challenge is not supported for your client", bufferedReader.readLine());

        bufferedWriter.write("WHISPER~test~random" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertEquals("ERROR~User is offline", bufferedReader.readLine());

        bufferedWriter.write("QUEUE" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertTrue(server.getQueuedPlayers().contains(clientHandler));
        bufferedWriter.write("QUEUE" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertFalse(server.getQueuedPlayers().contains(clientHandler));

        bufferedWriter.write("RANK" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        message = bufferedReader.readLine();
        assertEquals("RANK~ ~ ", message);

        bufferedWriter.write("LOGOUT" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        message = bufferedReader.readLine();
        assertEquals("ERROR~Unknown command", message);

        bufferedWriter.write("QUEUE" + "\n");
        bufferedWriter.flush();
        Thread.sleep(1000);
        assertTrue(server.getQueuedPlayers().contains(clientHandler));
        assertTrue(server.getAllUsers().contains("alex"));
        clientSocket.close();
        Thread.sleep(1000);
        assertFalse(server.getQueuedPlayers().contains(clientHandler));
        assertFalse(server.getAllUsers().contains("alex"));
    }
}
