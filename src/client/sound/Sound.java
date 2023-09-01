package client.sound;

import javax.sound.sampled.*;
import java.io.IOException;
import java.net.URL;

/**
 * This class provides methods for playing sound effects in a game.
 */
public class Sound {

    /**
     * Plays the given sound with the provided parameters.
     *
     * @param soundFileName The filename of the sound to play.
     * @param loop          If true, the sound will loop indefinitely.
     * @param volume        The volume at which to play the sound.
     *                      Float.MIN_VALUE will play the sound at default volume.
     * @ensures The sound will play as per the given parameters.
     * @throws UnsupportedAudioFileException If the audio file format is unsupported.
     * @throws LineUnavailableException      If the system cannot access the line.
     * @throws IOException                   If there's an issue reading the sound file.
     */
    private static void playSound(String soundFileName, boolean loop, float volume) {
        ClassLoader classLoader = Sound.class.getClassLoader();
        Thread newThread = new Thread(() -> {
            try {
                URL soundPath = classLoader.getResource(soundFileName);
                AudioInputStream audioInput = AudioSystem.getAudioInputStream(soundPath);
                Clip clip = AudioSystem.getClip();
                clip.open(audioInput);
                if (volume != Float.MIN_VALUE) {
                    FloatControl control = (FloatControl) clip.getControl(FloatControl.Type.MASTER_GAIN);
                    control.setValue(volume);
                }
                clip.start();

                if (loop) {
                    clip.loop(Clip.LOOP_CONTINUOUSLY);
                } else {
                    Thread.sleep(clip.getMicrosecondLength() / 1000);
                }

            } catch (UnsupportedAudioFileException e) {
                System.out.println("Unsupported Audio File");
            } catch (LineUnavailableException e) {
                System.out.println("Line Unavailable");
            } catch (IOException e) {
                System.out.println("Sound not found");
            } catch (InterruptedException e) {
                System.out.println("Interrupted Exception");
            }
        });
        newThread.start();
    }

    /**
     * Plays the background sound effect on loop.
     *
     * @ensures Background sound is playing in loop.
     */
    public static void backSound() {
        playSound("resources/back.wav", true, -25.0f);
    }

    /**
     * Plays the shot sound effect once.
     *
     * @ensures Shot sound effect is played once.
     */
    public static void shot() {
        playSound("resources/shot.wav", false, Float.MIN_VALUE);
    }

    /**
     * Plays the win sound effect once.
     *
     * @ensures Win sound effect is played once.
     */
    public static void winSound() {
        playSound("resources/win.wav", false, Float.MIN_VALUE);
    }

    /**
     * Plays the lost sound effect once.
     *
     * @ensures Lost sound effect is played once.
     */
    public static void lostSound() {
        playSound("resources/lost.wav", false, Float.MIN_VALUE);
    }

    /**
     * Plays the start game sound effect once.
     *
     * @ensures Start sound effect is played once.
     */
    public static void startSound() {
        playSound("resources/start.wav", false, Float.MIN_VALUE);
    }
}
