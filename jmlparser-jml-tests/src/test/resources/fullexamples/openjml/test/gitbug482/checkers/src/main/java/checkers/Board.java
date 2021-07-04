package checkers;
import java.awt.Point;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 *  Board logic
 */
public class Board
{

	public static final int EMPTY = 0;
	public static final int PAWN = 1;
	public static final int QUEEN = 2;

	public static final int width = 8;
	public static final int height = 8;

	public int turnHolder;

	private final int[] data;

	public Board()
	{

		turnHolder = 1;

		data = new int[width * height];

		for(int y = 0; y < 3; y++)
			for(int x = 0; x < width; x++)
				if((x ^ y) % 2 != 0)
					set(x, y, -1);

		for(int y = height - 3; y < height; y++)
			for(int x = 0; x < width; x++)
				if((x ^ y) % 2 != 0)
					set(x, y, 1);

	}

	public Board(Board board)
	{
		this.turnHolder = board.turnHolder;
		this.data = board.data.clone();
	}

	private void set(int x, int y, int piece)
	{
		assert (inBounds(x, y));
		data[y * width + x] = piece;
	}

	public int getPlayer(int x, int y)
	{
		return Utils.sign(get(x, y));
	}

	public int get(int x, int y)
	{
		if(!inBounds(x, y))
			return 0;
		else
			return data[y * width + x];
	}

	public boolean inBounds(Point p)
	{
		return inBounds(p.x, p.y);
	}

	public int get(Point p)
	{
		return get(p.x, p.y);
	}

	private void set(Point p, int v)
	{
		set(p.x, p.y, v);
	}

	public boolean inBounds(int x, int y)
	{
		return ((x ^ y) % 2) != 0 && x >= 0 && y >= 0 && x < width && y < height;
	}

	final static Point[] directions = { new Point(-1, -1), new Point(-1, 1), new Point(1, -1), new Point(1, 1) };

	public Move getMove(Point p0, Point p1)
	{

		for(Move m : getMoves())
		{
			if(p0.equals(m.p0) && p1.equals(m.p1))
				return m;
		}

		return null;

	}

	public List<Move> getMoves(Point p0)
	{
		List<Move> moves = new LinkedList<Move>();

		for(Move m : getMoves())
		{
			if(p0.equals(m.p0))
				moves.add(m);
		}

		return moves;

	}

	public List<Move> getMoves()
	{

		boolean mustJump = false;

		Point p0 = new Point();
		Point p1 = new Point();

		List<Move> moves = new ArrayList<Move>();

		for(p0.y = 0; p0.y < height; p0.y++)
			for(p0.x = 0; p0.x < width; p0.x++)
				if(getPlayer(p0) == turnHolder)
				{

					int range = 2;

					if(getPiece(p0) == QUEEN)
						range = Math.min(width, height);

					for(Point d : directions)
						for(int i = 1; i < range; i++)
						{
							p1.setLocation(p0);
							p1.translate(d.x * i, d.y * i);

							if(!inBounds(p1) || getPlayer(p1) == turnHolder)
								break;

							if(getPlayer(p1) == -turnHolder)
							{

								p1.translate(d.x, d.y);

								if(!inBounds(p1) || get(p1) != 0)
									break;

								moves.add(new Move(p0, p1, true));
								mustJump = true;
								break;

							}
							else
							{
								if(getPiece(p0) != QUEEN && d.y == turnHolder)
									break;

								moves.add(new Move(p0, p1, false));
							}

						}

				}

		if(mustJump)
		{
			List<Move> jumps = new LinkedList<Move>();

			for(Move m : moves)
			{
				if(m.jump)
					jumps.add(m);
			}

			return jumps;

		}

		return moves;

	}

	private int getPlayer(Point p0)
	{
		return Utils.sign(get(p0));
	}

	private int getPiece(Point p0)
	{
		return Math.abs(get(p0));
	}

	public void makeMove(Move move)
	{

		assert (getMove(move.p0, move.p1) != null);

		int piece = get(move.p0);

		if((move.p1.y == 0 && turnHolder == 1) || (move.p1.y == height - 1 && turnHolder == -1))
			piece = Utils.sign(piece) * 2;

		set(move.p0, 0);
		set(move.p1, piece);

		if(move.jump)
			set(move.getJumpedPiece(), 0);

		turnHolder = -turnHolder;

	}

	public Board clone()
	{
		return new Board(this);
	}

	public int getPiece(int x, int y)
	{
		return Math.abs(get(x, y));
	}

}
