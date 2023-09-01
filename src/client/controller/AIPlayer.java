package client.controller;

import client.model.AbstractPlayer;
import client.model.Board;
import client.model.Color;
import client.model.Game;
import client.model.Move;
import client.model.Player;
import java.io.BufferedReader;
import java.io.IOException;
import java.util.Random;

/**
 * AI player class.
 */
public class AIPlayer extends AbstractPlayer {
    private final BufferedReader reader;
    //@private invariant reader != null;

    /**
     * Creates a new AI player.
     *
     * @param color the color of the player
     * @param board the board of the game
     * @param name  the name of the player
     * @param reader the reader to read from
     */
    //@requires color == Color.RED || color == Color.BLUE || color == Color.EMPTY;
    /*@requires (\forall int i; (i >= 0 && i < board.SIZE * board.SIZE);
                    board.getFieldColor(i/board.SIZE, i%board.SIZE) != Color.EMPTY);    */
    //@requires !name.isEmpty() && name.length() <= 20 && reader != null;
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

            // Wait for server's response
            String data = reader.readLine();

            if (data.equals("GAMEOVER")) {
                System.out.println("The game has been finished.");
                return null;
            } else {
                return new Move(Integer.parseInt(data.split("~")[1]) / Board.SIZE,
                        Integer.parseInt(data.split("~")[1]) % Board.SIZE, getColor());
            }
        } catch (IOException e) {
            System.out.println("Error reading or sending the move. Please try again.");
            e.printStackTrace(); // This will print more details about the exception.
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
        Move winningMove = null;
        for (Move move : game.getValidMoves()) {
            Game hypotheticalGame = game.deepCopy(); // Assuming you have a deepCopy() method in the Game class
            hypotheticalGame.makeMove(move); // Assuming you have a makeMove() method in the Game class
            if (hypotheticalGame.isFinished() && hypotheticalGame.getWinner() == this) {
                winningMove = move;  // This move would make the AI player win
            }
        }
        if (winningMove != null) {
            return winningMove;
        } else {
            Random rand = new Random();
            int randomIndex = rand.nextInt(game.getValidMoves().size());
            return game.getValidMoves().get(randomIndex);
        }
    }

    /**
     * Returns copy of the player.
     * @return copy of the player
     */
    //@ensures this != \result;
    //@ensures \result != null;
    @Override
    public Player deepCopy() {
        Player player = new AIPlayer(getColor(), getBoard(), getName(), reader);
        player.setOpponent(getOpponent());
        return player;
    }
}
