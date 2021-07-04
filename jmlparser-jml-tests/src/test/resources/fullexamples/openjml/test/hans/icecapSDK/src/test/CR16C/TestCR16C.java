package test.CR16C;

import devices.CR16C.KT4585.Port;
import devices.CR16C.KT4585.WatchdogFreeze;

public class TestCR16C {

    /**
     * @param args
     */
    public static void main(String[] args) {
        Port P2 = new Port(0xFF4850);
        
        WatchdogFreeze wdog = new WatchdogFreeze(0xFF5000);
        wdog.set |= WatchdogFreeze.FRZ_WDOG;
        
        P2.mode &= ~Port.P2_1_MODE;
        P2.dir |= Port.Px_1_DIR;
        
        while(true)
        {
            P2.reset |= Port.Px_1_SET;
            devices.System.delay(5000);
            P2.set |= Port.Px_1_SET;
            devices.System.delay(5000);     
        }
    }
}
