package devices.ev3;

public class MotorPort extends Port {
	public enum MotorPortID {
		A, B, C, D
	}

	public MotorPort(MotorPortID portID) {
		switch (portID) {
		case A:
			port = 1;
			break;
		case B:
			port = 2;
			break;
		case C:
			port = 4;
			break;
		case D:
			port = 8;
			break;
		}
	}
}
