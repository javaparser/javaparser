package devices.NXT;

import vm.Address32Bit;
import vm.HardwareObject;

public class AT91_REG extends HardwareObject {
	public static final int AT91C_SPI_TXEMPTY = 0x200;     // (SPI) TXEMPTY Interrupt
	public static final int AT91C_PIO_PA12 = (1 << 12);    // Pin Controlled by PA12
	public static final int AT91C_PDC_TXTEN = (1 << 8);    // (PDC) Transmitter Transfer Enable
	
	public int reg;
	
	public AT91_REG(int address) {
		super(new Address32Bit(address));
	}
}
