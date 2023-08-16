package client.controller;

import client.model.*;

import java.io.BufferedReader;
import java.io.IOException;

/**
 * Real player class that does indicate moves.
 */
public class RealPlayer extends AbstractPlayer {
    private final BufferedReader reader1;
    //@private invariant reader1 != null;

    private final BufferedReader reader2;
    //@private invariant reader2 != null;

    /**
     * Creates a new AbstractPlayer player.
     *
     * @param color the color of the player
     * @param board the board of the game
     * @param name  the name of the player
     */
    public RealPlayer(Color color, Board board, String name, BufferedReader reader1, BufferedReader reader2) {
        super(color, board, name);
        this.reader1 = reader1;
        this.reader2 = reader2;
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
     * Gets the move from the console.
     * @param game the game
     * @return the move of the player
     * @throws IOException if you can't read from the reader
     */
    //@requires game != null && game.getBoard() != null && !game.isFinished();
    //@requires reader2 != null;
    //@ensures \result.getColor() == this.getColor() && \old(game.getValidMoves()).contains(\result);
    //@pure;
    private Move getMove(Game game) throws IOException {
        while (true) {
            try {
                //TODO: Add suggestion of move
                System.out.println("PLease enter the index of the field.");

                String command = reader2.readLine();

                int index = Integer.parseInt(command);
                Move move = new Move(index / Board.SIZE, index % Board.SIZE, getColor());

                if (!game.isValidMove(move)) {
                    System.out.println("Please enter a valid index");
                } else {
                    return move;
                }

            } catch (NumberFormatException e) {
                System.out.println("Index should be a numeric value.");
            }
        }
    }

    /**
     * Copies a player.
     * @return player
     */
    //@ensures this != \result;
    //@ensures \result != null;
    @Override
    public Player deepCopy() {
        Player player = new RealPlayer(getColor(), getBoard(), toString(), reader1, reader2);
        player.setOpponent(getOpponent());
        return player;
    }

}
