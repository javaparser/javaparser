package test.ev3;

import devices.ev3.EV3;
import devices.ev3.Motor;
import devices.ev3.MotorPort;
import devices.ev3.SensorPort;
import devices.ev3.UltraSonicSensor;
import devices.ev3.Motor.Direction;
import devices.ev3.MotorPort.MotorPortID;
import devices.ev3.SensorPort.SensorPortID;

public class Main {

	public static void main(String args[]) {
		testMotor();
		testSensor();
	}

	private static void testSensor() {
		SensorPort port = new SensorPort(SensorPortID.Port1);
		UltraSonicSensor ultraSonicSensor = new UltraSonicSensor(port);
		for (byte x = 0; x < 30; x++) {
			short sensorValue = ultraSonicSensor.getSensorValue();
			devices.Console.println("value = " + sensorValue);
			EV3.sleep(500);
		}
	}

	private static void testMotor() {
		MotorPort port = new MotorPort(MotorPortID.A);
		Motor m = new Motor(port);
		m.setPower((byte) 20);
		for (byte x = 0; x < 3; x++) {
			if (x % 2 == 0) {
				m.setDirection(Direction.FORWARD);
			}
			else {
				m.setDirection(Direction.BACKWARD);
			}
			m.start();
			EV3.sleep(1000);
			m.stop();
			EV3.sleep(1000);
		}
	}
}
