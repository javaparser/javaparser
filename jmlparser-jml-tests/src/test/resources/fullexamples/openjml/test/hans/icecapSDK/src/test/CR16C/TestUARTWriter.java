package test.CR16C;

import io.UARTWriter;

import java.io.IOException;

import devices.CR16C.KT4585.LED;
import devices.CR16C.KT4585.WatchdogFreeze;

public class TestUARTWriter {

    /**
     * @param args
     * @throws IOException 
     */
    public static void main(String[] args) throws IOException {
        LED led = new LED();
        UARTWriter writer = new UARTWriter();
        WatchdogFreeze wdog = new WatchdogFreeze(0xFF5000);
        wdog.set |= WatchdogFreeze.FRZ_WDOG;
        String tick = "Tick";
        writer.register();
        
        while (true) {
            led.on();
            devices.System.delay(10000);
            led.off();
            devices.System.delay(20000);
            writer.write(tick);
        }
    }
}
