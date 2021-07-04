package test.CR16C;

import devices.CR16C.KT4585.LED;
import devices.CR16C.KT4585.UARTL2Channel;
import devices.CR16C.KT4585.WatchdogFreeze;

public class TestL2 {
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		UARTL2Channel channel = new UARTL2Channel();
        WatchdogFreeze wdog = new WatchdogFreeze(0xFF5000);
        wdog.set |= WatchdogFreeze.FRZ_WDOG;
		LED led = new LED();

        while (true) {
            led.on();
            devices.System.delay(10000);
            led.off();
            devices.System.delay(20000);
            channel.write("hello my man! How are you? Are you ok?");
        }
	}
}
