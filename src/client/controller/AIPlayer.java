package client.controller;

import client.model.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.List;
import java.util.Random;

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
     * Determines the move of the AI player.
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
        System.out.println("It's AI move, " + getName() + ".");

        Move moveAI;
        try {
            moveAI = getMove(game);
            protocol.sendMove(moveAI.hashCode());
            //reads the move from the server
            String data = reader.readLine();
            //check if the game is over
            if (data.equals("GAMEOVER")) {
                System.out.println("The game has been finished.");
                return null;
            } else {
                return new Move(Integer.parseInt(data.split("~")[1]) / Board.SIZE,
                        Integer.parseInt(data.split("~")[1]) % Board.SIZE, getColor());
            }
        } catch (IOException e) {
            System.out.println("Error reading or sending the move. Please try again.");
            return null;
        }
    }

    /**
     * Gets the move from AI.
     * @param game the game
     * @return the move of the AI
     */
    //@requires game != null && game.getBoard() != null && !game.isFinished();
    //@ensures \result.getColor() == this.getColor() && \old(game.getValidMoves()).contains(\result);
    //@pure;
    private Move getMove(Game game) {
        Move winningMove = game.getWinningMove();
        if (winningMove != null) {
            return winningMove;
        }
        Random rand = new Random();
        int randomIndex = rand.nextInt(game.getValidMoves().size());
        return game.getValidMoves().get(randomIndex);
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
