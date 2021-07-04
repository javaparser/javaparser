package devices.ev3;

public class UltraSonicSensor {

	private static native short getSensor(byte sensor);
	
	private SensorPort port;

	public UltraSonicSensor(SensorPort port) {
		this.port = port;
	}

	public short getSensorValue() {
		return getSensor(port.getPort());
	}
}
