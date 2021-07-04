package checkers;
import java.awt.AlphaComposite;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.RenderingHints;
import java.util.Collections;
import java.util.List;

import javax.swing.JPanel;

/**
 *  Component displaying state of the board
 */
public class BoardView extends JPanel
{

	static class CurrentMoveState
	{
		Point piece = new Point();
		Point position = new Point();
		Point offset = new Point();
		List<Move> possibleMoves = Collections.emptyList();
	}
	
	private static final long serialVersionUID = -1441037602815044777L;

	Board board;

	CurrentMoveState currentMove = null;
	
	public BoardView(Board b)
	{

		setBoard(b);

		final int size = 32;
		setPreferredSize(new Dimension(size * Board.width, size * Board.height));
		setSize(getPreferredSize());
		setBackground(Color.red);

	}

	public synchronized void animateMove(final Move move)
	{

		currentMove = new CurrentMoveState();
		
		currentMove.piece = move.p0;
		currentMove.offset = new Point(0, 0);
		currentMove.position = new Point();

		int frames = 30;
		
		for(int i = 0; i < frames; i++)
		{
			
			currentMove.position.x = (move.p0.x * (frames - i) + move.p1.x * i) * 32 / frames;
			currentMove.position.y = (move.p0.y * (frames - i) + move.p1.y * i) * 32 / frames;
			repaint();
			
			try
			{
				Thread.sleep(1000 / 60);
			}
			catch(InterruptedException e)
			{
				break;
			}

			
		}			
		
		currentMove = null;
	
	}

	@Override
	public void paint(Graphics g)
	{

		if(g instanceof Graphics2D)
			((Graphics2D)g).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

		final Color evenColor = new Color(0xfece9e);
		final Color oddColor = new Color(0xd08c47);

		for(int y = 0; y < Board.height; y++)
		{
			for(int x = 0; x < Board.width; x++)
			{
				if(((x ^ y) & 1) == 0)
					g.setColor(evenColor);
				else
					g.setColor(oddColor);		

				g.fillRect(x * 32, y * 32, 32, 32);

			}
		}

		for(int y = 0; y < Board.height; y++)
		{
			for(int x = 0; x < Board.width; x++)
			{
				if(currentMove==null || currentMove.piece.x != x || currentMove.piece.y != y)
					drawPiece(g, x * 32, y * 32, board.get(x, y));
			}
		}

		if(currentMove != null)
		{

			if(g instanceof Graphics2D)
			{

				((Graphics2D)g).setComposite(AlphaComposite.getInstance(AlphaComposite.SRC_OVER, 0.2f));

				if(currentMove.possibleMoves != null)
					for(Move m : currentMove.possibleMoves)
					{
						drawPiece(g, m.p1.x * 32, m.p1.y * 32, board.get(currentMove.piece.x, currentMove.piece.y));

					}

				((Graphics2D)g).setComposite(AlphaComposite.getInstance(AlphaComposite.SRC_OVER));

			}

			drawPiece(g, currentMove.position.x + currentMove.offset.x, currentMove.position.y + currentMove.offset.y, board.get(currentMove.piece.x, currentMove.piece.y));

		}

	}

	private void drawPiece(Graphics g, Color fg, Color bg, int piece)
	{

		final int m = 2;
		final int p = 6;

		g.setColor(bg);
		g.fillOval(m, m, 31 - m * 2, 31 - m * 2);
		g.setColor(fg);
		g.drawOval(m, m, 31 - m * 2, 31 - m * 2);
		g.drawOval(p, p, 31 - p * 2, 31 - p * 2);

		if(piece == 2)
		{
			g.drawLine(12, 16, 19, 16);
			g.drawLine(12, 15, 19, 15);
			g.drawLine(15, 12, 15, 19);
			g.drawLine(16, 12, 16, 19);
		}
	}

	private void drawPiece(Graphics g, int x, int y, int piece)
	{

		g.translate(x, y);

		switch(Utils.sign(piece))
		{
			case 0:
				break;
			case 1:
				drawPiece(g, Color.BLACK, Color.WHITE, Math.abs(piece));
				break;
			case -1:
				drawPiece(g, Color.WHITE, Color.BLACK, Math.abs(piece));
				break;
		}

		g.translate(-x, -y);

	}

	public void setBoard(Board board)
	{
		this.board = board;
		currentMove = null;
		repaint();
	}

	public Board getBoard()
	{
		return board;
	}


}
