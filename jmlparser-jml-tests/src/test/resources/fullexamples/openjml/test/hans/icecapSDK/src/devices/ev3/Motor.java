package devices.ev3;

public class Motor {

	public enum Direction {
		FORWARD, BACKWARD
	}

	public static final byte opOUTPUT_POWER = (byte) 0xA4;
	public static final byte opOUTPUT_START = (byte) 0xA6;
	public static final byte opOUTPUT_STOP = (byte) 0xA3;

	private static native void setMotor(byte cmd, byte p1, byte p2);

	private MotorPort port;
	private byte power;

	public Motor(MotorPort port) {
		this.port = port;
	}

	public void setPower(byte power) {
		if (power > 100) {
			power = 100;
		}
		if (power < 0) {
			power = 0;
		}
		this.power = power;

		setMotor(opOUTPUT_POWER, port.getPort(), power);
	}

	public void start() {
		setMotor(opOUTPUT_START, port.getPort(), (byte) 0);
	}

	public void stop() {
		setMotor(opOUTPUT_STOP, port.getPort(), (byte) 0);
	}

	public void setDirection(Direction direction) {
		byte adjustment = 1;
		switch (direction) {
		case FORWARD:
			if (power < 0) {
				adjustment = -1;
			}
			break;
		case BACKWARD:
			if (power > 0) {
				adjustment = -1;
			}
			break;
		}
		if (adjustment == -1) {
			power = (byte) (adjustment * power);
			setMotor(opOUTPUT_POWER, port.getPort(), power);
		}
	}
}
