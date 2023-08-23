package server.view;

import server.controller.Server;

import java.util.InputMismatchException;
import java.util.Scanner;

/**
 * The Main class that starts the server.
 */
public class ServerTUI {
    /**
     * Starts the server.
     * @param args the arguments
     */
    public static void main(String[] args) {
        int port;
        while (true) {
            try {
                Scanner scanner = new Scanner(System.in);
                System.out.println("Enter reference port number:");
                port = scanner.nextInt();
                if (port < 0 || port > 65535) {
                    System.out.println("Your indicated port number is not correct.");
                } else {
                    break;
                }
            } catch (InputMismatchException e) {
                System.out.println("Invalid characters");
            }
        }
        Server server = new Server(port);
        server.start();
        Scanner scanner = new Scanner(System.in);
        while (true) {
            System.out.println("`STOP` - to stop the server");
            String command = scanner.nextLine();
            if (command.equalsIgnoreCase("STOP")) {
                server.stop();
                break;
            }
        }
    }
}
