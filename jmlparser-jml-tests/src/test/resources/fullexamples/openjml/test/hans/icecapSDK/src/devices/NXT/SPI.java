package devices.NXT;

import vm.Address32Bit;
import vm.HardwareObject;

// Serial Peripheral Interface (SPI), see SAM7S256 data sheet, Table 28-3.

public class SPI extends HardwareObject
{
  public int SPI_CR;
  public int SPI_MR;
  public int SPI_RDR;
  public int SPI_TDR;
  public int SPI_SR;
  public int SPI_IER;
  public int SPI_IDR;
  public int SPI_IMR;
  @SuppressWarnings("unused")
  private int reserved0;
  @SuppressWarnings("unused")
  private int reserved1;
  @SuppressWarnings("unused")
  private int reserved2;
  @SuppressWarnings("unused")
  private int reserved3;
  public int SPI_CSR0;
  public int SPI_CSR1;
  public int SPI_CSR2;
  public int SPI_CSR3;
  
  public static PDC spiPDC;  // PDC offset: 0x100, cf. Table 28-3
  
  public SPI (int address, int PDC_offset)
  {
    super(new Address32Bit(address));
    spiPDC = new PDC (address + PDC_offset);
  }
}
