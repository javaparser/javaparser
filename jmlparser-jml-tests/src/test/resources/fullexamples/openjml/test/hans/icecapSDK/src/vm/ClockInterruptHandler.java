package vm;

import javax.scj.util.Const;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import devices.CR16C.KT4585.CR16CInterruptDispatcher;
import devices.i86.I86InterruptDispatcher;

/* Add setScheduler(Scheduler sch)  */
public class ClockInterruptHandler implements InterruptHandler, ProcessLogic {
	private Process currentProcess;
	private vm.Scheduler scheduler;

	@IcecapCVar
	private static boolean hvmClockReady;

	private static byte disableCount = 1;

	@Override
	@IcecapCompileMe
	public void run() {
		while (true) {
			currentProcess = (Process) scheduler.getNextProcess();
			enable();
			handlerProcess.transferTo(currentProcess);
		}
	}

	@Override
	public void catchError(Throwable t) {
		Const.reporter.schedulerError(t);
	}

	private Process handlerProcess;

	private ClockInterruptHandler(Scheduler scheduler, int[] stack) {
		setScheduler(scheduler);
		handlerProcess = new vm.Process(this, stack);
		handlerProcess.initialize();
	}

	@IcecapCompileMe
	@Override
	public void handle() {
		disable();
		currentProcess.transferTo(handlerProcess);
	}

	@IcecapCompileMe
	@Override
	public void disable() {
		disableCount++;
		hvmClockReady = false;

	}

	@IcecapCompileMe
	@Override
	public void enable() {
		disableCount--;
		if (disableCount == 0) {
			hvmClockReady = true;
		}
	}

	public static ClockInterruptHandler instance;

	@IcecapCompileMe
	public static void initialize(Scheduler scheduler, int[] stack) {
		switch (Machine.architecture) {
		case Machine.X86_64:
		case Machine.X86_32:
			I86InterruptDispatcher.init();
			break;
		case Machine.CR16_C:
			CR16CInterruptDispatcher.init();
			break;
		}
		instance = new ClockInterruptHandler(scheduler, stack);
	}

	public void yield() {
		handle();
	}

	@Override
	public void register() {
		InterruptDispatcher
				.registerHandler(this, InterruptDispatcher.HVM_CLOCK);
	}

	public void startClockHandler(Process process) {
		this.currentProcess = process;
	}

	public void setScheduler(Scheduler sch) {
		this.scheduler = sch;
		if (Machine.getCurrentScheduler() == sch) {
			/* Hack to force inclusion of service methods */
			/* This code should never actually be executed */
			Monitor.notify(null);
			Monitor.wait(null);
			Monitor.notifyAll(null);
		}
		Machine.setCurrentScheduler(sch);
	}
}