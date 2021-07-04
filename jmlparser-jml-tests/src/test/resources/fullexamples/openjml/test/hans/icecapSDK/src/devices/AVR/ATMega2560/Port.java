package devices.AVR.ATMega2560;

import vm.Address32Bit;
import vm.HardwareObject;

public class Port extends HardwareObject
{
    public static final int DDRA = 0x001;
    public static final int DDRB = 0x004;
    public static final int DDRC = 0x007;
    public static final int DDRD = 0x00A;
    public static final int DDRE = 0x00D;
    public static final int DDRF = 0x010;
    public static final int DDRG = 0x013;
    public static final int DDRL = 0x10a;

    public byte ddr;
    public byte data;

    public Port(int address) {
        super(new Address32Bit(address));
    }
}
