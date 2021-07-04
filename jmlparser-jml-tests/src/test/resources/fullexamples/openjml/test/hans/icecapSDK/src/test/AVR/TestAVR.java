package test.AVR;

import devices.AVR.ATMega2560.Port;
import devices.AVR.ATMega2560.Timer;

public class TestAVR {

    static int delay;

    static {
        delay = 50;
    }

    private static void delay(int cycles) {
        for (int i = 0; i < cycles; i++) {
            ;
        }
    }

    public static void main(String[] args) {
        Port portA = new Port(Port.DDRA);
        portA.ddr = (byte) 0xff;
        
        Timer2Handler handler = new Timer2Handler(portA);
        
        handler.register();
        
        Timer.timerInit();
        
        while (true) {
            byte msbNibble = (byte) (portA.data & 0xf0);
            byte lsbNibble = (byte) (portA.data & 0x0f);
            portA.data = (byte) ((~msbNibble) | lsbNibble);
            delay(delay);
        }
    }
}
