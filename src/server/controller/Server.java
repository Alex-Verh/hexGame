package server.controller;

import client.model.Player;
import server.PlayerChatLacking;
import server.PlayerOfflineException;
import server.model.GameServer;

import java.io.BufferedWriter;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.util.*;

/**
 * Server class that manages client connections and broadcasts messages.
 */
public class Server implements Runnable{

    private ServerSocket serverSocket;
    //@private invariant serverSocket != null;

    private final int port;
    //@ private invariant port > 0 && port <= 65535;

    private final List<Socket> clients;
    //@ private invariant clients != null;

    private final List<GameServer> games;
    //@private invariant games != null;

    private final Map<ClientHandler, String> players;
    //@private invariant !players.isEmpty();

    private final List<ClientHandler> queuedPlayers;
    //@ private invariant queuedPlayers != null;

    private final Map<String, Integer> rankings;
    //@private invariant rankings != null;
    /**
     * Initializes a new Server.
     * @param port the port number to listen on.
     */
    //@ requires port > 0 && port <= 65535;
    public Server(int port) {
        this.port = port;
        this.clients = new ArrayList<>();
        this.players = new HashMap<>();
        this.queuedPlayers = new ArrayList<>();
        this.games = new ArrayList<>();
        this.rankings = new HashMap<>();
    }

    /**
     * Starts the server to listen for client connections.
     */
    public void start() {
        Thread serverThread = new Thread(() -> {
            try (ServerSocket serverSocket = new ServerSocket(port)) {
                System.out.println("Server started on port: " + port);

                while (!Thread.currentThread().isInterrupted()) {
                    Socket clientSocket = serverSocket.accept();
                    ClientHandler client = new ClientHandler(clientSocket, this);
                    Thread clientThread = new Thread(client);
                    clientThread.start();
                }
            } catch (IOException e) {
                System.out.println("Server error: " + e.getMessage());
            }
        });

        serverThread.start();
    }

    /**
     * Adds a client to the server.
     * @param client adds the client to the server
     */
    //@requires client != null && client.getName().length() <= 20;
    //@ensures players.containsKey(client);
    public void addClient(ClientHandler client) {
        synchronized (players) {
            players.put(client, client.getName());
        }
    }

    //@requires client != null;
    /*@ensures !queuedPlayers.contains(client) &&
            !clients.contains(client.getClientSocket()) && !players.containsKey(client); */
    //@ensures client.getClientSocket().isClosed();
    public synchronized void removeClient(ClientHandler client) {
        synchronized (clients) {
            clients.remove(client.getClientSocket());
        }
        synchronized (players) {
            players.remove(client);
        }
        synchronized (queuedPlayers) {
            queuedPlayers.remove(client);
        }
        try {
            client.getClientSocket().close();
        } catch (IOException e) {
            System.out.println("Client has disconnected");
        }
    }

    public synchronized List<String> getAllUsers() {
        List<String> userNames = new ArrayList<>();
        for (ClientHandler client : players.keySet()) {
            userNames.add(client.getClientName());
        }
        return userNames;
    }

    /**
     * Adds client to the queue.
     * @param clientHandler the client to add
     */
    //@requires clientHandler != null;
    //@ensures queuedPlayers.size() - 1 == \old(queuedPlayers.size());
    public void addToQueue(ClientHandler clientHandler) {
        synchronized (queuedPlayers) {

            queuedPlayers.add(clientHandler);

            if (queuedPlayers.size() == 2) {

                GameServer gameServer =
                        new GameServer(queuedPlayers.get(0), queuedPlayers.get(1), this);

                queuedPlayers.remove(0);
                queuedPlayers.remove(0);
                addGameServer(gameServer);
                new Thread(gameServer).start();
            }
        }
    }

    /**
     * Switches in or out of queue.
     * @param clientHandler the client to switch
     */
    //@requires clientHandler != null;
    /*@ensures queuedPlayers.size() + 1 == \old(queuedPlayers.size()) ||
            queuedPlayers.size() -1 == \old(queuedPlayers.size());  */
    public void switchQueue(ClientHandler clientHandler) throws IOException {
        if (queuedPlayers.contains(clientHandler)) {
            removeFromQueue(clientHandler);
            //DEBUG
            System.out.println("Remove client from queue");
        } else {
            addToQueue(clientHandler);
        }
    }

    /**
     * Adds client to the queue.
     * @param clientHandler the client to add
     */
    //@requires clientHandler != null;
    //@ensures queuedPlayers.size() - 1 == \old(queuedPlayers.size());
    public void removeFromQueue(ClientHandler clientHandler) throws IOException {
        synchronized (queuedPlayers) {
            queuedPlayers.remove(clientHandler);
        }
    }


    public synchronized void broadcastChatMessage(String message, String senderName) {
        // Loop through each client and send the chat message.
        for (ClientHandler client : players.keySet()) {
            // Avoid sending the message back to the sender.
            if (!client.getClientName().equals(senderName)) {
                try {
                    BufferedWriter writer = client.getSocketWriter();
                    Protocol.sendChat(writer, senderName, message);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
    }

    public List<ClientHandler> getQueuedPlayers() {
        return queuedPlayers;
    }

    /**
     * Sends a whisper to a specific client.
     * @param data the message to send
     * @param username the username of the sender
     * @throws PlayerOfflineException if the user is not online
     * @throws PlayerChatLacking if the user is not able to be whispered to
     */
    //@requires username.length() <= 20 && !username.isEmpty();
    //@requires !data.isEmpty();
    //@pure;
    public void whisper(String data, String username, BufferedWriter socketOut)
            throws PlayerOfflineException, PlayerChatLacking, IOException {
        String[] split = data.split("~");
        synchronized (players) {
            // checks if the user is online
            // else throws OfflineException
            if (players.containsValue(split[1])) {
                for (ClientHandler client : players.keySet()) {
                    if (client.getClientName().equals(split[1])) {
                        // checks if the user can be whispered to
                        // else throws WhisperException
                        if (client.isChatEnabled()) {
                            client.sendWhisper(data, username); // sends the whisper
                        } else {
                            Protocol.sendCannotWhisper(socketOut, username);
                            throw new PlayerChatLacking(username);
                        }
                    }
                }
            } else {
                Protocol.sendCannotWhisper(socketOut, username);
                throw new PlayerOfflineException(username);
            }
        }
    }

    /**
     * Checks if user is not busy.
     * @param username the name of the user
     * @return true if the user is in a game, false otherwise
     */
    public boolean isInGame(String username) {
        synchronized (games) {
            for (GameServer game : games) {
                if (game.getPlayers().get(0).equals(username) ||
                        game.getPlayers().get(1).equals(username)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Adds a game to the list
     * @param gameServer to be added in the list
     */
    //@requires gameServer != null;
    //@ensures games.size() + 1 == \old(games.size());
    public void addGameServer(GameServer gameServer) {
        synchronized (games) {
            games.add(gameServer);
        }
    }

    /**
     * Removes a game from the list
     * @param gameServer to be removed from the list
     */
    //@requires gameServer != null;
    //@ensures games.size() - 1 == \old(games.size());
    public void removeGameServer(GameServer gameServer) {
        synchronized (games) {
            games.remove(gameServer);
        }
    }

    /**
     * Gets the rankings.
     * @return the rankings
     */
    /*@ensures (\forall String key; rankings.containsKey(key);
        rankings.get(key) >= 0); */
    //@pure;
    public Map<String, Integer> getRankings() {
        synchronized (rankings) {
            Map<String, Integer> rank = new HashMap<>();
            for (String key : this.rankings.keySet()) {
                rank.put(key, this.rankings.get(key));
            }
            return rank;
        }
    }

    /**
     * Stops the server.
     */
    //@ensures serverSocket.isClosed();
    //@pure;
    public void stop() {
        synchronized (clients) {
            try {
                serverSocket.close();
                for (Socket client : clients) {
                    client.close();
                }
            } catch (IOException e) {
                System.out.println("Server could not be stopped");
            }
        }
    }

    /**
     * Handles connections and creates new clientHandlers.
     */
    //@pure;
    @Override
    public void run() {
        while (true) {
            try {
                Socket socket = serverSocket.accept();
                synchronized (clients) {
                    clients.add(socket);
                    System.out.println(clients.size() + " clients connected");
                }
                ClientHandler clientHandler = new ClientHandler(socket, this);
                new Thread(clientHandler).start();

            } catch (SocketException e) {
                System.out.println("Server stopped");
                break;
            } catch (IOException e) {
                System.out.println("Client could not connect");
            }
        }
    }
}
