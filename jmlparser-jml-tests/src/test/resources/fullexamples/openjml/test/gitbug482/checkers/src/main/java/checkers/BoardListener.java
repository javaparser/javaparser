package checkers;

/**
 * Observer for board events
 */
public interface BoardListener
{
	/**
	 * called before `move` is made on `board`
	 */
	public void onMove(Board board, Move move);

	/**
	 * called when new game button has been pressed
	 * @param board - new board
	 */
	public void onNewGame(Board board);

}