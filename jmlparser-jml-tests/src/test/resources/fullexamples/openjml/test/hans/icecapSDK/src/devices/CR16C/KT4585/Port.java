package devices.CR16C.KT4585;

import vm.Address32Bit;
import vm.HardwareObject;

public class Port extends HardwareObject {
    
    public static final short P2_1_MODE = 0x000C;
    public static final short Px_1_DIR = 0x000C;
    
    public static final short Px_1_SET = 0x02;
    public static final short Px_1_RESET = 0x02;
    
    public short data;
    public short set;
    public short reset;
    public short dir;
    public short mode;
    
    public Port(int address) {
        super(new Address32Bit(address));
    }

}
