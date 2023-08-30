import client.controller.Protocol;
import org.junit.jupiter.api.*;

import java.io.*;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests that verifies if the actual results correspond to the expected outputs and if they are sent correctly to the server.
 */
class ProtocolTest {
    private Protocol protocol;
    private Socket socket;
    private Socket clientSocket;
    private OutputStream outputStream;
    private OutputStreamWriter outputStreamWriter;
    private BufferedWriter bufferedWriter;

    /**
     * Sets up the protocol.
     * @throws IOException when it doesn't connect
     */
    @BeforeEach
    public void setUp() throws IOException {
        ServerSocket serverSocket = new ServerSocket(0);

        socket = new Socket("localhost", serverSocket.getLocalPort());
        clientSocket = serverSocket.accept();
        outputStream = socket.getOutputStream();
        outputStreamWriter = new OutputStreamWriter(outputStream);
        bufferedWriter = new BufferedWriter(outputStreamWriter);
        protocol = new Protocol(socket);
    }

    /**
     * Tests if HELLO message is sent correctly and can be read from the server.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testHello() throws IOException {
        // create input and output streams for the server-client socket
        InputStream inputStream = clientSocket.getInputStream();
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(inputStream));

        // send a HELLO message from the client
        boolean helloSent = protocol.sendHello();
        assertTrue(helloSent);

        // server receives the message
        String message = bufferedReader.readLine();
        assertEquals("HELLO~AlexClient~RANK~CHAT", message);
    }

    /**
     * Tests if sending a username is successful.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendUsername() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        boolean loginSuccessful = protocol.sendUsername("valid_username");
        assertTrue(loginSuccessful);
        assertEquals("LOGIN~valid_username", bufferedReader.readLine());

    }

    /**
     * Tests if the message has been sent to the server.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendMessage() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        protocol.sendMessage("Hello");
        assertEquals("CHAT~Hello", bufferedReader.readLine());

    }


    /**
     * Tests if the whisper been sent to the server.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendWhisper() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        protocol.sendWhisper("Hello", "valid_username");
        assertEquals("WHISPER~Hello~valid_username", bufferedReader.readLine());

    }

    /**
     * Tests if rank was sent correctly
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendRank() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        protocol.sendRank();
        assertEquals("RANK", bufferedReader.readLine());
    }

    /**
     * Tests if the QUEUE command has been sent to the server.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendQUEUE() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        protocol.sendQueue();
        assertEquals("QUEUE", bufferedReader.readLine());
    }

    /**
     * Tests if the LIST command has been sent to the server.
     * @throws IOException when it doesn't connect
     */
    @Test
    void testSendLIST() throws IOException {
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));

        protocol.sendList();
        assertEquals("LIST", bufferedReader.readLine());
    }

    /**
     * closes the socket and the streams.
     * @throws IOException when it can't close
     */
    @AfterEach
    public void closing() throws IOException {
        bufferedWriter.close();
        outputStreamWriter.close();
        outputStream.close();
        socket.close();
        clientSocket.close();
    }
}