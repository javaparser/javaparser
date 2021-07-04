package checkers;

public class HumanPlayer implements Player
{

	public String toString()
	{
		return "Human";
	}

	public boolean isHuman()
	{
		return true;
	}

	public Move getMove(Board board)
	{
		throw new IllegalStateException();
	}
}
