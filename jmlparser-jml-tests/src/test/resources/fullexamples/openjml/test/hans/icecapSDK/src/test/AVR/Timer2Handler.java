package test.AVR;

import vm.InterruptDispatcher;
import vm.InterruptHandler;
import devices.AVR.ATMega2560.ATMega2560InterruptDispatcher;
import devices.AVR.ATMega2560.Port;

public class Timer2Handler implements InterruptHandler {
    private Port portA;
    
    public Timer2Handler(Port portA){
        this.portA = portA;
    }

    @Override
    public void handle() {
        byte msbNibble = (byte) (portA.data & 0xf0);
        byte lsbNibble = (byte) (portA.data & 0x0f);
        portA.data = (byte) (msbNibble | (~lsbNibble)); 
    }

	@Override
	public void register() {
        ATMega2560InterruptDispatcher.init();
        InterruptDispatcher.registerHandler(new Timer2Handler(portA), ATMega2560InterruptDispatcher.TIMER2_OVF);
	}

	@Override
	public void enable() {
	}

	@Override
	public void disable() {
	}
}
