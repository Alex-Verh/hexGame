package client.controller;

import client.model.*;

import java.io.BufferedReader;

public class AIPlayer extends AbstractPlayer {
    private final BufferedReader reader;
    //@private invariant reader != null;

    /**
     * Creates a new AI player.
     *
     * @param color the color of the player
     * @param board the board of the game
     * @param name  the name of the player
     */
    public AIPlayer(Color color, Board board, String name, BufferedReader reader) {
        super(color, board, name);
        this.reader = reader;
    }

    /**
     * Determines the move of the player.
     * @param game the game
     * @param protocol the sender that is used to send messages to the server
     * @return the move of the player
     */
    //@requires game != null && protocol != null;
    //@requires game.getBoard() != null && !game.isFinished();
    //@ensures game.getValidMoves().contains(\result);
    //@pure;
    @Override
    public Move move(Game game, Protocol protocol) {
        return null;
    }

    /**
     * Returns copy of the player.
     * @return copy of the player
     */
    //@ensures this != \result;
    //@ensures \result != null;
    @Override
    public Player deepCopy() {
        Player player = new AIPlayer(getColor(), getBoard(), toString(), reader);
        player.setOpponent(getOpponent());
        return player;
    }
}
