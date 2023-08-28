package client.controller;

import client.model.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class NetworkPlayer extends AbstractPlayer {
    private final BufferedReader serverReader;
    //@private invariant serverReader != null;

    /**
     * Creates a new NetworkPlayer.
     *
     * @param color   the mark of the player
     * @param board  the board of the game
     * @param name   the name of the player
     * @param serverReader the reader to read from
     */
    //@requires color == Color.EMPTY || color == Color.BLUE || color == Color.RED;
    /*@requires (\forall int i; (i >= 0 && i < board.SIZE * board.SIZE);
                board.getFieldColor(i/board.SIZE, i%board.SIZE) != Color.EMPTY); */
    //@requires !name.isEmpty() && serverReader != null && name.length() <= 20;
    public NetworkPlayer(Color color, Board board, String name, BufferedReader serverReader) {
        super(color, board, name);
        this.serverReader = serverReader;
    }

    /**
     * Determines move of a player.
     *
     * @param game the game
     * @param protocol the sender to send the move to the server
     * @return move
     */
    //@requires game != null && protocol != null;
    //@requires game.getBoard() != null && !game.isFinished();
    //@ensures game.getValidMoves().contains(\result);
    //@pure;
    @Override
    public Move move(Game game, Protocol protocol) {
        try {
            // Read the move from the server
            String data = serverReader.readLine();

            if (data.equals("GAMEOVER")) {
                return null;
            } else {
                String[] split = data.split("~");
                int index = Integer.parseInt(split[1]);

                //return the move
                return new Move(index / Board.SIZE, index % Board.SIZE, getColor());
            }
        } catch (IOException e) {
            System.out.println("Player has disconnected");
            return null;
        }
    }

    /**
     * Copies a player.
     *
     * @return player
     */
    //@ensures this != \result;
    //@ensures \result != null;
    @Override
    public Player deepCopy() {
        Player player = new NetworkPlayer(getColor(), getBoard(), toString(), serverReader);
        player.setOpponent(getOpponent());
        return player;
    }
}
