package checkers;
import java.awt.Font;

import javax.swing.JTextArea;

public class Log extends JTextArea implements BoardListener
{

	private static final long serialVersionUID = -6714540903699673108L;

	public Log()
	{
		super(8, 0);
		setEditable(false);
		setFont(new Font(Font.MONOSPACED, Font.BOLD, 12));
	}

	@Override
	public void onMove(Board board, Move move)
	{
		append(move + "\n");
		setCaretPosition(getText().length());
	}

	@Override
	public void onNewGame(Board board)
	{
		setText("");
	}

}
