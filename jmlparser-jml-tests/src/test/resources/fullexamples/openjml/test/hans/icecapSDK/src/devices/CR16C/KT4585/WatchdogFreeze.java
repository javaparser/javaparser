package devices.CR16C.KT4585;

import vm.Address32Bit;
import vm.HardwareObject;

public class WatchdogFreeze extends HardwareObject {

    public static final short FRZ_WDOG = 0x0008;
    
    public short set;
    public short reset;
    
    public WatchdogFreeze(int address) {
        super(new Address32Bit(address));
    }

}
