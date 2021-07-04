package checkers;
import java.util.List;
import java.util.Random;

/**
 * AI `Player` which picks random moves 
 */
public class RandomPlayer implements Player
{

	private final Random rand = new Random();

	@Override
	public Move getMove(Board board)
	{
		List<Move> moves = board.getMoves();

		if(moves.isEmpty())
			return null;

		return moves.get(rand.nextInt(moves.size()));
	}

	@Override
	public boolean isHuman()
	{
		return false;
	}

	@Override
	public String toString()
	{
		return "Random";
	}

}
