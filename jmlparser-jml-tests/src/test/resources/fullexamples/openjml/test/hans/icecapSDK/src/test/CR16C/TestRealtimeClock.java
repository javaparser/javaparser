package test.CR16C;

import io.UARTWriter;

import java.io.IOException;

import devices.CR16C.KT4585.CR16CRealtimeClock;
import devices.CR16C.KT4585.LED;

public class TestRealtimeClock {

	public static void main(String args[]) throws IOException {
		LED led = new LED();
		CR16CRealtimeClock clock = (CR16CRealtimeClock) vm.RealtimeClock.getRealtimeClock();
		UARTWriter writer = new UARTWriter();
		writer.register();
		String tick = "Tick";
		
		while (true) {
			led.on();
			devices.System.delay(40000);
			led.off();
			devices.System.delay(40000);
			writer.writeShort(clock.getTickCount());
			writer.write(tick);
		}
	}
}
