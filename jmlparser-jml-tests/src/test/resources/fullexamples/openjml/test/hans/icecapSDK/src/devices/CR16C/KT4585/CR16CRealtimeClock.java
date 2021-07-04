package devices.CR16C.KT4585;

import icecaptools.IcecapCompileMe;

import javax.realtime.AbsoluteTime;

import vm.InterruptDispatcher;
import vm.InterruptHandler;


public class CR16CRealtimeClock extends vm.RealtimeClock implements InterruptHandler {

	private DeviceRegShort INT1_PRIORITY_REG;
	private DeviceRegShort TIMER1_RELOAD_N_REG;
	private DeviceRegShort TIMER_CTRL_REG;
	private DeviceRegShort RESET_INT_PENDING_REG;
	private static final short TIM1_MODE = 0x20;
	private static final short TIM1_CTRL = 0x2;
	private static final short CLK_CTRL1 = 0x08;
	private static final short TIM1_INT_PEND = 0x100;

	private short tickCount;

	/* TODO: Create real Process for handling this interrupt */
	/* Should be the same as the scheduling clock */
	public CR16CRealtimeClock() {
		INT1_PRIORITY_REG = new DeviceRegShort(0xFF5406);
		TIMER1_RELOAD_N_REG = new DeviceRegShort(0xFF497A);
		TIMER_CTRL_REG = new DeviceRegShort(0xFF4970);
		RESET_INT_PENDING_REG = new DeviceRegShort(0xFF5402);
		INT1_PRIORITY_REG.reg |= 0x1;
		TIMER1_RELOAD_N_REG.reg = 11520;
		TIMER_CTRL_REG.reg = TIM1_MODE | TIM1_CTRL | CLK_CTRL1;

		tickCount = 0;
	}

	@Override
	public int getGranularity() {
		return 100 * 1000000;
	}

	@Override
	public void getCurrentTime(AbsoluteTime now) {
		now.set(tickCount * 100);
	}

	@IcecapCompileMe
	@Override
	public void handle() {
		tickCount++;
		RESET_INT_PENDING_REG.reg |= TIM1_INT_PEND;
	}

	public short getTickCount() {
		return tickCount;
	}

	@Override
	public void register() {
		CR16CInterruptDispatcher.init();
		InterruptDispatcher.registerHandler(this, (byte) 24);
	}

	@Override
	public void enable() {
	}

	@Override
	public void disable() {
	}
}
