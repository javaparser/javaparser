package devices.CR16C.KT4585;

import vm.InterruptDispatcher;
import vm.InterruptHandler;

public class CR16CInterruptDispatcher extends InterruptDispatcher {

    public static final byte NMI_INT = 1;
    public static final byte SVC_TRAP = 5;
    public static final byte DVZ_TRAP = 6;
    public static final byte FLG_TRAP = 7;
    public static final byte BPT_TRAP = 8;
    public static final byte TRC_TRAP = 9;
    public static final byte UND_TRAP = 10;
    public static final byte IAD_TRAP = 12;
    public static final byte DBG_TRAP = 14;
    public static final byte ISE_INT = 15;
    public static final byte ACCESS12_INT = 16;
    public static final byte KEYB_INT = 17;
    public static final byte RESERVED_INT = 18;
    public static final byte CT_CLASSD_INT = 19;
    public static final byte UART_RI_INT = 20;
    public static final byte UART_TI_INT = 21;
    public static final byte SPI_INT = 22;
    public static final byte TIM0_INT = 23;
    public static final byte TIM1_INT = 24;
    public static final byte CLK100_INT = 25;
    public static final byte DIP_INT = 26;
    public static final byte AD_INT = 27;
    public static final byte SPI2 = 28;
    public static final byte DSP_INT = 29;

    private CR16CInterruptDispatcher() {
	}
    
    public static void init() {
        if (!InterruptDispatcher.init) {
            InterruptDispatcher.numberOfInterrupts = 31;
            InterruptDispatcher.handlers = new InterruptHandler[numberOfInterrupts];
            InterruptDispatcher.init();
            InterruptDispatcher.init = true;
        }
    }
}
