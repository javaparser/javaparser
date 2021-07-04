package vm;

import reflect.ObjectInfo;
import icecaptools.IcecapCompileMe;

public class Process {
	private ProcessLogic logic;
	private int[] stack;
	private ProcessExecutor processExecuter;
	private SP sp;
	private int runtime_data;

	private static StackAnalyser stackAnalyser;
	
	private boolean isFinished;

	public boolean isFinished() {
		return isFinished;
	}

	@IcecapCompileMe
	public Process(ProcessLogic logic, int[] stack) {
		this.logic = logic;
		this.stack = stack;
		this.isFinished = false;
		processExecuter = new ProcessExecutor(this);
		switch (Machine.architecture) {
		case Machine.X86_64:
			sp = new X86_64SP();
			break;
		case Machine.CR16_C:
		case Machine.X86_32:
		default:
			sp = new X86_32SP();
			break;
		}
		if (stackAnalyser != null)
		{
			stackAnalyser.addStack(stack);
		}
	}

	@IcecapCompileMe
	public void transferTo(Process nextProcess) {
		transfer(this, nextProcess);
	}

	public final void initialize() {
		executeWithStack(processExecuter, stack);
	}

	private static native void transfer(Process currentProcess,
			Process nextProcess);

	private static native void executeWithStack(Runnable runnable,
			int[] schedulerStack);

	private static class ProcessExecutor implements Runnable {
		private Process thisProcess;
		private boolean isStarted;

		ProcessExecutor(Process thisProcess) {
			this.thisProcess = thisProcess;
		}

		@Override
		@IcecapCompileMe
		public void run() {
			isStarted = false;
			thisProcess.transferTo(thisProcess);
			if (!isStarted) {
				isStarted = true;
			} else {
				try {
					thisProcess.logic.run();
				} catch (Throwable t) {
					thisProcess.logic.catchError(t);
				}
				vm.ClockInterruptHandler.instance.yield();
				thisProcess.isFinished = true;
				for (;;)
					;
			}
		}
	}

	private static abstract class SP {
		public abstract int getCSP();

		public abstract int getJSP();
	}

	private static class X86_32SP extends SP {
		public int csp;
		public int jsp;

		@Override
		public int getCSP() {
			return csp;
		}

		@Override
		public int getJSP() {
			return jsp;
		}
	}

	private static class X86_64SP extends SP {
		public long csp;
		public long jsp;

		@Override
		public int getCSP() {
			return (int) csp;
		}

		@Override
		public int getJSP() {
			return (int) jsp;
		}
	}

	public int[] getStack() {
		return stack;
	}

	public short getJavaStackTop() {
		int top = sp.getJSP();
		return getIndex(top);
	}

	public int getCStackTop() {
		int top = sp.getCSP();
		return getIndex(top);
	}

	private short getIndex(int top) {
		return (short) ((top - ObjectInfo.getAddress(stack)) >> 2);
	}
	
	public static void enableStackAnalysis()
	{
		stackAnalyser = new FullStackAnanlyser();
	}
	
	public static void reportStackUsage()
	{
		if (stackAnalyser != null)
		{
			stackAnalyser.reportStackUsage();
		}
	}
	
}
