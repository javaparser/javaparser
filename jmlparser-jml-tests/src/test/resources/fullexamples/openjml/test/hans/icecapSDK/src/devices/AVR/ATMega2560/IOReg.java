package devices.AVR.ATMega2560;

import vm.Address32Bit;
import vm.HardwareObject;

public class IOReg extends HardwareObject {

    /* Constants */
    public static final byte TOIE2 = 0x0;
    public static final byte EXCLK = 0x6;
    public static final byte AS2 = 0x5;
    public static final byte CS21 = 0x1;    
    public static final byte TCR2BUB = 0x0;
    public static final byte TOV2 = 0x0;
    
    /* Addresses */
    public static final int TIMSK2 = 0x70; 
    public static final int ASSR = 0xb6;
    public static final int TCNT2 = 0xb2;
    public static final int TCCR2B = 0xb1;
    public static final int TIFR2 = 0x17;

    public byte reg;
    
    public IOReg(int address) {
        super(new Address32Bit(address));
    }
}
