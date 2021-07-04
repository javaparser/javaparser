package devices.CR16C.KT4585;

import vm.Address32Bit;
import vm.HardwareObject;

public class DeviceRegShort extends HardwareObject {
    
    public static final short UART_TI_INT_PRIO = 0x0070;
    public static final short UART_TI_INT_PEND = 0x0020;
    
    public short reg;
    
    public DeviceRegShort(int address) {
        super(new Address32Bit(address));
    }

}
