package checkers;
import java.util.Collections;
import java.util.List;

public class MinMaxPlayer implements Player
{

	private final int level;

	public MinMaxPlayer(int level)
	{
		this.level = level;
	}

	public Move getMove(Board board)
	{
		return getMove(board, level);
	}

	private Move getMove(Board board, int depth)
	{

		List<Move> moves = board.getMoves();

		Collections.shuffle(moves);

		Move bestMove = null;

		for(Move move : moves)
		{
			Board child = board.clone();
			child.makeMove(move);

			if(depth < 1 && !move.jump)
				move.score = -eval(child);
			else
			{
				Move result = getMove(child, depth - 1);
				if(result == null)
					move.score = Integer.MAX_VALUE;
				else
					move.score = -result.score;
			}

			if(depth == 6)
				System.out.println(move);

			if(bestMove == null || move.score > bestMove.score)
				bestMove = move;

		}

		return bestMove;

	}

	private static int eval(Board board)
	{

		int player = 0;
		int opponent = 0;

		for(int y = 0; y < Board.height; y++)
			for(int x = 0; x < Board.width; x++)
				if(board.getPlayer(x, y) == board.turnHolder)
					player += board.getPiece(x, y);
				else
					opponent += board.getPiece(x, y);

		return player - opponent;

	}

	@Override
	public String toString()
	{
		return "MinMax ("+level+")";
	}
	
	@Override
	public boolean isHuman()
	{
		return false;
	}

}
