package checkers;
import java.awt.EventQueue;
import java.awt.Point;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.util.LinkedList;
import java.util.List;

/**
 *  handles board events, human and AI moves, delivers events to BoardListeners
 */
public class BoardController
{

	private class BoardMouseAdapter implements MouseListener, MouseMotionListener
	{

		@Override
		public void mousePressed(MouseEvent e)
		{
			if(e.getButton() == MouseEvent.BUTTON1 && isHumanMove())
			{
				int x = e.getX() / 32;
				int y = e.getY() / 32;

				if(getBoard().inBounds(x, y) && getBoard().getPlayer(x, y) == getBoard().turnHolder)
				{

					view.currentMove = new BoardView.CurrentMoveState();

					view.currentMove.piece = new Point(x, y);
					view.currentMove.position = e.getPoint();
					view.currentMove.offset = new Point(x * 32 - view.currentMove.position.x, y * 32 - view.currentMove.position.y);

					view.currentMove.possibleMoves = getBoard().getMoves(view.currentMove.piece);

					view.repaint();
				}

			}

		}

		@Override
		public void mouseReleased(MouseEvent e)
		{
			if(e.getButton() == MouseEvent.BUTTON1 && isHumanMove() && view.currentMove != null)
			{
				int x = (e.getX() + view.currentMove.offset.x + 16) / 32;
				int y = (e.getY() + view.currentMove.offset.y + 16) / 32;

				Move move = getBoard().getMove(view.currentMove.piece, new Point(x, y));

				if(move != null)
					makeMove(move);
				else
					view.currentMove = null;

				view.repaint();

			}
		}

		@Override
		public void mouseMoved(MouseEvent e)
		{
		}

		@Override
		public void mouseClicked(MouseEvent e)
		{
		}

		@Override
		public void mouseEntered(MouseEvent e)
		{
		}

		@Override
		public void mouseExited(MouseEvent e)
		{
		}

		@Override
		public void mouseDragged(MouseEvent e)
		{
			if(isHumanMove() && view.currentMove != null)
			{
				view.currentMove.position.setLocation(e.getX(), e.getY());
				view.repaint();
			}
		}

	}

	private final Player[] players = new Player[] { new HumanPlayer(), new HumanPlayer() };

	private final BoardView view;

	private Thread backgroundThread;

	private final List<BoardListener> boardListeners = new LinkedList<BoardListener>();

	public BoardController(BoardView view)
	{

		this.view = view;

		BoardMouseAdapter mouse_adapter = new BoardMouseAdapter();

		view.addMouseListener(mouse_adapter);
		view.addMouseMotionListener(mouse_adapter);

	}

	public Board getBoard()
	{
		return view.getBoard();
	}

	public boolean isHumanMove()
	{
		return getCurrentPlayer().isHuman();
	}

	private Player getCurrentPlayer()
	{
		return players[getBoard().turnHolder > 0 ? 1 : 0];
	}

	void requestMove()
	{

		interruptBackgroundThread();
		
		if(isHumanMove())
			return;

		if(getBoard().getMoves().isEmpty())
			return;
		
		backgroundThread = new Thread(new Runnable()
		{

			@Override
			public void run()
			{

				Move move = getCurrentPlayer().getMove(getBoard());

				view.animateMove(move);

				makeMove(move);
			}
		});

		backgroundThread.start();

	}

	void makeMove(final Move move)
	{

		for(BoardListener listener : boardListeners)
		{
			listener.onMove(getBoard(), move);
		}

		getBoard().makeMove(move);

		view.repaint();

		EventQueue.invokeLater(new Runnable()
		{

			@Override
			public void run()
			{
				requestMove();
			}
		});

	}

	private void interruptBackgroundThread()
	{
		if(backgroundThread != null)
		{

			try
			{
				backgroundThread.interrupt();
				backgroundThread.join();
			}
			catch(InterruptedException e)
			{
				throw new Error(e);
			}
		}
	}

	public void newGame()
	{

		if(backgroundThread != null)
			interruptBackgroundThread();

		view.setBoard(new Board());

		for(BoardListener listener : boardListeners)
		{
			listener.onNewGame(getBoard());
		}

	}

	public void setPlayer(int id, Player player)
	{

		boolean repeatRequestMove = isHumanMove();
		
		players[(id + 1) / 2] = player;

		if(repeatRequestMove)
			requestMove();
	}

	public void addBoardListener(BoardListener listener)
	{
		boardListeners.add(listener);
	}

}
