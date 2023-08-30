import client.controller.Listener;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import server.controller.Server;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.net.ServerSocket;
import java.net.Socket;

import static org.junit.jupiter.api.Assertions.*;

/**
 *  Tests correct functionality of the Listener class responsible for listening to the server and providing messages to the player.
 */
class ListenerTest {

    private Listener listener;
    private BufferedReader bufferedReader;
    private Socket socket2;

    /**
     * Sets up the listener
     * @throws IOException when does not connect
     */
    @BeforeEach
    public void setUp() throws IOException {
        SystemExitPreventer.preventSystemExit();

        ServerSocket serverSocket = new ServerSocket(0);
        // create a mock socket
        Socket socket1 = new Socket(serverSocket.getInetAddress(), serverSocket.getLocalPort());
        socket2 = serverSocket.accept();


        // create a piped writer and reader
        PipedWriter writer = new PipedWriter();
        PipedReader reader = new PipedReader(writer);
        bufferedReader = new BufferedReader(reader);

        // create a new listener
        listener = new Listener(socket1, writer);
    }

    /**
     * Tests if the listener correctly sends messages to the game
     * @throws IOException when it doesn't connect
     * @throws InterruptedException when the thread is interrupted
     */
    @Test
    void testListener() throws IOException, InterruptedException {

        // start the listener in a new thread
        Thread listenerThread = new Thread(listener);
        listenerThread.start();

        // send a message to the listener
        socket2.getOutputStream().write("MOVE~12\n".getBytes());
        // wait for the message to be written to the piped writer
        Thread.sleep(100);

        // read the message from the piped reader
        String message = bufferedReader.readLine();


        // assert that the message was correctly sent to the game
        assertEquals("MOVE~12", message);

        // send a message to the listener
        socket2.getOutputStream().write("NEWGAME~user1~user2\n".getBytes());
        // wait for the message to be written to the piped writer
        Thread.sleep(100);

        // read the message from the piped reader
        message = bufferedReader.readLine();

        // assert that the message was correctly sent to the game
        assertEquals("NEWGAME~user1~user2", message);

        // send a message to the listener
        socket2.getOutputStream().write("GAMEOVER~DRAW\n".getBytes());
        // wait for the message to be written to the piped writer
        Thread.sleep(100);

        // read the message from the piped reader
        message = bufferedReader.readLine();

        // assert that the message was correctly sent to the Game (GameOver because the game can calculate the winner and doesn't need the server for that)
        assertEquals("GAMEOVER", message);

        socket2.close();

        listenerThread.join();
    }

    /**
     * Tests if the rank is correctly printed
     */
    @Test
    void testPrintRank() {
        String rank = "RANK~bobDylan~25~alex~10~lym~5";
        String expected = "Rank of all the players:\n" +
                "bobDylan: 25\n" +
                "alex: 10\n" +
                "lym: 5";
        assertEquals(expected, Listener.printRank(rank));
    }

    /**
     * Tests if the list is correctly printed
     */
    @Test
    void testPrintList() {
        String list = "LIST~jacco~alex~jeroen~bob~boris~tom";
        String expected = "List of all the players:\n" +
                "jacco, alex, jeroen, bob, boris\n" +
                "tom";
        assertEquals(expected, Listener.printList(list));
    }
}