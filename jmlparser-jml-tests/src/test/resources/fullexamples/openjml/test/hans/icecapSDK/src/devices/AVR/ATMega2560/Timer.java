package devices.AVR.ATMega2560;


public class Timer {

    private static IOReg TIMSK2;
    private static IOReg ASSR;
    private static IOReg TCNT2;
    private static IOReg TCCR2B;
    private static IOReg TIFR2;
    
    static
    {
        TIMSK2 = new IOReg(IOReg.TIMSK2);
        ASSR = new IOReg(IOReg.ASSR);
        TCNT2 = new IOReg(IOReg.TCNT2);
        TCCR2B = new IOReg(IOReg.TCCR2B);
        TIFR2 = new IOReg(IOReg.TIFR2);
    }
    
    public native static void enableGlobalInterrupt();
    
    public static void timerInit()
    {
        /* Disable the Timer/Counter2 interrupts by clearing OCIE2 and TOIE2 */
        TIMSK2.reg &= ~(1 << IOReg.TOIE2);
        
        /* Select external 32kHz clock source by setting AS2 as appropriate */
        /* For this to work on STK600 you need to place a jumper between the 32KHz and TOSC1 pin on the AUX header */
        ASSR.reg |= (1 << IOReg.EXCLK);
        ASSR.reg |= (1 << IOReg.AS2);
        
        /* Write new values to TCNT2, OCR2, and TCCR2 */
        TCNT2.reg = 0;
        TCCR2B.reg |= (1 << IOReg.CS21);
        
        /* To switch to asynchronous operation: Wait for TCN2UB, OCR2UB, and TCR2UB */
        while ((ASSR.reg & (1 << IOReg.TCR2BUB)) > 0)
            ;
        
        /* Clear the Timer/Counter2 Interrupt Flags */
        TIFR2.reg |= (1 << IOReg.TOV2);
        
        /* Enable Timer2 Overflow interrupt */
        TIMSK2.reg |= (1 << IOReg.TOIE2);
        
        enableGlobalInterrupt();
    }
}
