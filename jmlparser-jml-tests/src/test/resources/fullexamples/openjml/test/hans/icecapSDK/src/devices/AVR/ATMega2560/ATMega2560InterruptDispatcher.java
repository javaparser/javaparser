package devices.AVR.ATMega2560;

import vm.InterruptDispatcher;
import vm.InterruptHandler;

public class ATMega2560InterruptDispatcher extends InterruptDispatcher {

	public static final byte INT0 = 2; // $0002
	public static final byte INT1 = 3; // $0004
	public static final byte INT2 = 4; // $0006
	public static final byte INT3 = 5; // $0008
	public static final byte INT4 = 6; // $000A
	public static final byte INT5 = 7; // $000C
	public static final byte INT6 = 8; // $000E
	public static final byte INT7 = 9; // $0010
	public static final byte PCINT0 = 10; // $0012
	public static final byte PCINT1 = 11; // $0014
	public static final byte PCINT2 = 12; // $0016
	public static final byte WDT = 13; // $0018
	public static final byte TIMER2_COMPA = 14; // $001A
	public static final byte TIMER2_COMPB = 15; // $001C
	public static final byte TIMER2_OVF = 16; // $001E
	public static final byte TIMER1_CAPT = 17; // $0020
	public static final byte TIMER1_COMPA = 18; // $0022
	public static final byte TIMER1_COMPB = 19; // $0024
	public static final byte TIMER1_COMPC = 20; // $0026
	public static final byte TIMER1_OVF = 21; // $0028
	public static final byte TIMER0_COMPA = 22; // $002A
	public static final byte TIMER0_COMPB = 23; // $002C
	public static final byte TIMER0_OVF = 24; // $002E
	public static final byte SPI = 25; // $0030
	public static final byte USART0_RX = 26; // $0032
	public static final byte USART0_UDRE = 27; // $0034
	public static final byte USART0_TX = 28; // $0036
	public static final byte ANALOG_COMP = 29; // $0038
	public static final byte ADC = 30; // $003A
	public static final byte EE_READY = 31; // $003C
	public static final byte TIMER3_CAPT = 32; // $003E
	public static final byte TIMER3_COMPA = 33; // $0040
	public static final byte TIMER3_COMPB = 34; // $0042
	public static final byte TIMER3_COMPC = 35; // $0044
	public static final byte TIMER3_OVF = 36; // $0046
	public static final byte USART1_RX = 37; // $0048
	public static final byte USART1_UDRE = 38; // $004A
	public static final byte USART1_TX = 39; // $004C
	public static final byte TWI = 40; // $004E
	public static final byte SPM_READY = 41; // $0050
	public static final byte TIMER4_CAPT = 42; // $0052
	public static final byte TIMER4_COMPA = 43; // $0054
	public static final byte TIMER4_COMPB = 44; // $0056
	public static final byte TIMER4_COMPC = 45; // $0058
	public static final byte TIMER4_OVF = 46; // $005A
	public static final byte TIMER5_CAPT = 47; // $005C
	public static final byte TIMER5_COMPA = 48; // $005E
	public static final byte TIMER5_COMPB = 49; // $0060
	public static final byte TIMER5_COMPC = 50; // $0062
	public static final byte TIMER5_OVF = 51; // $0064
	public static final byte USART2_RX = 52; // $0066
	public static final byte USART2_UDRE = 53; // $0068
	public static final byte USART2_TX = 54; // $006A
	public static final byte USART3_RX = 55; // $006C
	public static final byte USART3_UDRE = 56; // $006E
	public static final byte USART3_TX = 57; // $0070

	private ATMega2560InterruptDispatcher() {
	}

	public static void init() {
		InterruptDispatcher.numberOfInterrupts = 57;
		InterruptDispatcher.handlers = new InterruptHandler[numberOfInterrupts];
		InterruptDispatcher.init();
	}
}
