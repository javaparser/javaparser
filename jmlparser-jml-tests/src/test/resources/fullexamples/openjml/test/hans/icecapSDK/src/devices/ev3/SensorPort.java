package devices.ev3;

public class SensorPort extends Port {

	public enum SensorPortID {
		Port1, Port2, Port3, Port4
	}

	public SensorPort(SensorPortID portID) {
		switch (portID) {
		case Port1:
			port = 0;
			break;
		case Port2:
			port = 1;
			break;
		case Port3:
			port = 2;
			break;
		case Port4:
			port = 3;
			break;
		}
	}
}
