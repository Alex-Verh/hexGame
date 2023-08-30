import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import server.controller.Protocol;

import java.io.*;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;


/**
 * Tests the server protocol.
 */
class SProtocolTest {

    BufferedWriter swriter;
    BufferedReader sreader;

    /**
     * Sets up the test.
     * @throws IOException if an I/O error occurs
     */
    @BeforeEach
    public void setup() throws IOException {
        PipedWriter writer = new PipedWriter();
        swriter = new BufferedWriter(writer);
        sreader = new BufferedReader(new PipedReader(writer));

    }

    /**
     * Tests the hello method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void helloTest() throws IOException {
        Protocol.hello(swriter);
        assertEquals("HELLO~AlexServer~CHAT~RANK", sreader.readLine());
    }

    /**
     * Tests the logedIn method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void logedInTest() throws IOException {
        Protocol.loggedIn(swriter);
        assertEquals("LOGIN", sreader.readLine());
    }

    /**
     * Tests the sendMove method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendMoveTest() throws IOException {
        Protocol.sendMove(swriter, 0);
        assertEquals("MOVE~0", sreader.readLine());
    }

    /**
     * Tests the sendNewGame method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendNewGameTest() throws IOException {
        Protocol.sendNewGame(swriter, "user1", "user2");
        assertEquals("NEWGAME~user1~user2", sreader.readLine());
    }

    /**
     * Tests the victory method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void victoryTest() throws IOException {
        Protocol.victory(swriter, "user1");
        assertEquals("GAMEOVER~VICTORY~user1", sreader.readLine());
    }

    /**
     * Tests the draw method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void drawTest() throws IOException {
        Protocol.draw(swriter);
        assertEquals("GAMEOVER~DRAW", sreader.readLine());
    }

    /**
     * Tests the disconnect method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void disconnectTest() throws IOException {
        Protocol.disconnect(swriter, "user1");
        assertEquals("GAMEOVER~DISCONNECT~user1", sreader.readLine());
    }

    /**
     * Tests the error method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void errorTest() throws IOException {
        Protocol.error(swriter, "error");
        assertEquals("ERROR~error", sreader.readLine());
    }

    /**
     * Tests the sendChat method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendChatTest() throws IOException {
        Protocol.sendChat(swriter, "user1", "message");
        assertEquals("CHAT~user1~message", sreader.readLine());
    }

    /**
     * Tests the sendWhisper method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendWhisperTest() throws IOException {
        Protocol.sendWhisper(swriter, "user1", "message");
        assertEquals("WHISPER~user1~message", sreader.readLine());
    }

    /**
     * Tests the sendList method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendListTest() throws IOException {
        List<String> list = List.of("user1", "user2");
        Protocol.sendList(swriter, list);
        assertEquals("LIST~user1~user2", sreader.readLine());
    }

    /**
     * Tests the ALREADYLOGGEDIN method.
     * @throws IOException if an I/O error occurs
     */
    @Test
    void sendALREADYLOGGEDINTest() throws IOException {
        Protocol.sendALREADYLOGGEDIN(swriter);
        assertEquals("ALREADYLOGGEDIN", sreader.readLine());
    }
}
