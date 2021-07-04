package devices.i86;

import vm.InterruptDispatcher;
import vm.InterruptHandler;

public class I86InterruptDispatcher extends InterruptDispatcher {
	
    private I86InterruptDispatcher() {
	}
    
	public static void init() {
        if (!InterruptDispatcher.init) {
            InterruptDispatcher.numberOfInterrupts = 1;
            InterruptDispatcher.handlers = new InterruptHandler[numberOfInterrupts];
            InterruptDispatcher.init();
            InterruptDispatcher.init = true;
        }
    }
}
