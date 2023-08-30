import client.model.Color;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

 class ColorTest {

    @Test
     void testGetOppositeColor() {
        assertEquals(Color.RED, Color.BLUE.getOppositeColor(), "Opposite of BLUE should be RED");
        assertEquals(Color.BLUE, Color.RED.getOppositeColor(), "Opposite of RED should be BLUE");
        assertEquals(Color.EMPTY, Color.EMPTY.getOppositeColor(), "Opposite of EMPTY should be EMPTY");
    }

    @Test
     void testGetColor() {
        assertEquals(Color.RED, Color.RED.getColor(), "RED's color should be RED");
        assertEquals(Color.BLUE, Color.BLUE.getColor(), "BLUE's color should be BLUE");
        assertEquals(Color.EMPTY, Color.EMPTY.getColor(), "EMPTY's color should be EMPTY");
    }
}
