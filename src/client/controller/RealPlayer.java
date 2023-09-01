package client.controller;

import client.model.*;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.Random;

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
    //@requires color == Color.RED || color == Color.BLUE || color == Color.EMPTY;
    /*@requires (\forall int i; (i >= 0 && i < board.SIZE * board.SIZE);
                    board.getFieldColor(i/board.SIZE, i%board.SIZE) != Color.EMPTY);    */
    //@requires !name.isEmpty() && name.length() <= 20 && reader1 != null && reader2 != null;
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
        System.out.println("It's your move, " + getName() + ".");

        Move playerMove;
        try {
            playerMove = getMove(game);
            protocol.sendMove(playerMove.hashCode());
            //reads the move from the server
            String data = reader2.readLine();
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
     * Gets the move from the console.
     * @param game the game
     * @return the move of the player
     * @throws IOException if you can't read from the reader
     */
    //@requires game != null && game.getBoard() != null && !game.isFinished();
    //@requires reader1 != null;
    //@ensures \result.getColor() == this.getColor() && \old(game.getValidMoves()).contains(\result);
    //@pure;
    private Move getMove(Game game) throws IOException {
        while (true) {
            try {
                System.out.println("Please enter the index of the field or 'suggest' for a suggestion.");


                synchronized(reader1) {
                    Move swapMove = new Move(9, 0 , getColor());
                    if (game.isValidMove(swapMove)) {
                        System.out.println("SWAP move is possible! Write `swap` to use it.");
                    }

                    String command = reader1.readLine();

                    if ("suggest".equalsIgnoreCase(command)) {
                        Move suggestedMove = suggestMove(game);
                        int suggestedIndex = suggestedMove.hashCode();
                        System.out.println("Suggested move: " + suggestedIndex);
                        game.getBoard().displayBoard();
                    } else {
                        if ("swap".equalsIgnoreCase(command)) {
                            return swapMove;
                        }
                        int index = Integer.parseInt(command);
                        Move move = new Move(index / Board.SIZE, index % Board.SIZE, getColor());

                        if (!game.isValidMove(move)) {
                            System.out.println("Please enter a valid index");
                        } else {
                            return move;
                        }
                    }

                }
            } catch (NumberFormatException e) {
                System.out.println("Index should be a numeric value.");
            }
        }
    }

    /**
     * Sugessts a move by a random logic to a player.
     * @param game is being played
     * @return move
     */
    //@requires game != null && game.getBoard() != null && !game.isFinished();
    //@ensures game.getValidMoves().contains(\result);
    public Move suggestMove(Game game) {
        Move winningMove = null;
        for (Move move : game.getValidMoves()) {
            Game hypotheticalGame = game.deepCopy(); // Assuming you have a deepCopy() method in the Game class
            hypotheticalGame.makeMove(move); // Assuming you have a makeMove() method in the Game class
            if (hypotheticalGame.isFinished() && hypotheticalGame.getWinner() == this) {
                winningMove = move;  // This move would make the player win
                break;  // No need to check further once we've found a winning move
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
