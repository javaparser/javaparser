package devices.ev3;

public class Button {

	public enum ButtonID {
		 UP, CENTER, DOWN, RIGHT, LEFT, BACK
	}
	
	private static native byte getButton(byte button);
	
	private byte button;
	
	public Button(ButtonID buttonID)
	{
		switch (buttonID)
		{
		case UP:	
			button = 0;
			break;
		case CENTER:	
			button = 1;
			break;
		case DOWN:	
			button = 2;
			break;
		case RIGHT:	
			button = 3;
			break;
		case LEFT:	
			button = 4;
			break;
		case BACK:	
			button = 5;
			break;
		}
	}

	public boolean isPressed() {
		return (getButton(button) > 0);
	}
}
