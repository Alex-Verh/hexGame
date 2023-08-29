package client;

import javax.sound.sampled.*;
import java.io.IOException;
import java.net.URL;

public class Sound {

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

    public static void backSound() {
        playSound("resources/back.wav", true, -25.0f);
    }

    public static void shot() {
        playSound("resources/shot.wav", false, Float.MIN_VALUE);
    }

    public static void winSound() {
        playSound("resources/win.wav", false, Float.MIN_VALUE);
    }

    public static void lostSound() {
        playSound("resources/lost.wav", false, Float.MIN_VALUE);
    }

    public static void startSound() {
        playSound("resources/start.wav", false, Float.MIN_VALUE);
    }
}
