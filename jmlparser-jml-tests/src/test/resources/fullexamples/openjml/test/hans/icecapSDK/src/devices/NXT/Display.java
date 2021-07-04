package devices.NXT;

import reflect.ObjectInfo;

public class Display
{
  private static AT91_REG AT91C_PIOA_SODR;  
  private static AT91_REG AT91C_PIOA_CODR;

  private byte[] buf;

  private static SPI spi;

  private static byte displayLineNumbers[][] = 
    { { (byte) 0xB0, 0x10, 0x00 },
      { (byte) 0xB1, 0x10, 0x00 }, 
      { (byte) 0xB2, 0x10, 0x00 },
      { (byte) 0xB3, 0x10, 0x00 }, 
      { (byte) 0xB4, 0x10, 0x00 },
      { (byte) 0xB5, 0x10, 0x00 }, 
      { (byte) 0xB6, 0x10, 0x00 },
      { (byte) 0xB7, 0x10, 0x00 } };

  Display ()
  {
    AT91C_PIOA_SODR = new AT91_REG(0xFFFFF430);    
    AT91C_PIOA_CODR = new AT91_REG(0xFFFFF434); 
    
    spi = new SPI(0xFFFE0000, 0x100);
    
    buf = new byte[1];
  }

  public void gotoLine (byte lineNo)
  {
    displayWrite(displayLineNumbers[lineNo], true);
  }

  private void put (byte b)
  {
    displayWait();
    buf[0] = b;
    displayWrite(buf, false);
  }

  private static void displayWait ()
  {
    while ((spi.SPI_SR & AT91_REG.AT91C_SPI_TXEMPTY) == 0)
    {
      ;
    }
  }

  private boolean displayWrite (byte[] pData, boolean isCmd)
  {
    boolean result = false;
    if ((spi.SPI_SR & AT91_REG.AT91C_SPI_TXEMPTY) > 0)
    {
      if (isCmd)
      {
        AT91C_PIOA_CODR.reg = AT91_REG.AT91C_PIO_PA12;
      }
      else
      {
        AT91C_PIOA_SODR.reg = AT91_REG.AT91C_PIO_PA12;
      }

      int bufferAddress = ObjectInfo.getAddress(pData);
      bufferAddress += 4; // Add header and array count
      
      SPI.spiPDC.TPR  = bufferAddress;
      SPI.spiPDC.TCR  = pData.length;
      SPI.spiPDC.PTCR = AT91_REG.AT91C_PDC_TXTEN;

      result = true;
    }
    return result;
  }

  public void print (byte b)
  {
    put(b);
  }

  public void print (char c)
  {
    byte[] buf = C64Font.get(c);
    displayWait();
    displayWrite(buf, false);
  }

  public void print (String s)
  {
    char[] arr = s.toCharArray();
    for (int i = 0; i < arr.length; i++)
      print(arr[i]);
  }
  
  /**
   * 
   * @param lineNo Linenumber, 0 <= no < 8
   * @param s  The string to print; 0 < s.length <= 12
   */
  public void printAt(byte lineNo, String s)
  {
    gotoLine (lineNo);
    print(s);      
  }
}
