package devices.NXT;

import vm.Address32Bit;
import vm.HardwareObject;

// Peripheral DMA Controller (PDC), see SAM7S256 data sheet, Table 22-1.

public class PDC extends HardwareObject
{
  public int RPR;
  public int RCR;
  public int TPR;
  public int TCR;
  public int RNPR;
  public int RNCR;
  public int TNPR;
  public int TNCR;
  public int PTCR;
  public int PTSR;
  
  public PDC (int address)
  {
    super(new Address32Bit(address));
  }

}
