package test.CR16C;

import vm.InterruptDispatcher;
import vm.InterruptHandler;
import devices.CR16C.KT4585.CR16CInterruptDispatcher;
import devices.CR16C.KT4585.DeviceRegShort;
import devices.CR16C.KT4585.LED;
import devices.CR16C.KT4585.WatchdogFreeze;

public class TestUART {

    static DeviceRegShort uart_clear_tx_int_reg;
    static DeviceRegShort uart_ctrl_reg;
    static DeviceRegByte uart_rx_tx_reg;
    
    public static class UARTTXHandler implements InterruptHandler {
        @Override
        public void handle() {
            uart_rx_tx_reg.reg = 'x';
            uart_ctrl_reg.reg |= 0x2;
            uart_clear_tx_int_reg.reg = 0;
        }

		@Override
		public void register() {
			CR16CInterruptDispatcher.init();
	        InterruptDispatcher.registerHandler(this, (byte) 21);			
		}

		@Override
		public void enable() {
		}

		@Override
		public void disable() {
		}
    }

    /**
     * @param args
     */
    public static void main(String[] args) {
        WatchdogFreeze wdog = new WatchdogFreeze(0xFF5000);
        wdog.set |= WatchdogFreeze.FRZ_WDOG;

        LED led = new LED();

        uart_clear_tx_int_reg = new DeviceRegShort(0xFF4904);
        uart_ctrl_reg = new DeviceRegShort(0xFF4900);
        uart_rx_tx_reg = new DeviceRegByte(0xFF4902);
        
        UARTTXHandler handler = new UARTTXHandler();
        handler.register();
        
        uart_rx_tx_reg.reg = 'x';
        uart_ctrl_reg.reg |= 0x2;
        uart_clear_tx_int_reg.reg = 0;

        while (true) {
            led.on();
            devices.System.delay(10000);
            led.off();
            devices.System.delay(10000);
        }
    }
}
