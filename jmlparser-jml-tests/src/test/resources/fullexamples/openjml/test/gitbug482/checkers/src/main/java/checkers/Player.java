package checkers;
public interface Player
{

	/**
	 * @return true if player is controlled by human, and will not make moves with `getMove`
	 */
	public boolean isHuman();

	/**
	 * @param board - current board
	 * @return - calculated move
	 */
	Move getMove(Board board);

}
