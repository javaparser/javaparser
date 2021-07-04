package thread;

import vm.Monitor;
import vm.Process;
import vm.Scheduler;

public class JavaLangThreadScheduler implements Scheduler {

	private static class JavaLangThreadMonitor extends vm.Monitor {
		private int mutex;
		private int conditionVariable;

		JavaLangThreadMonitor() {
			initializeMutex();
		}

		private native void initializeMutex();

		@Override
		public void lock() {
			if (mutex != 0) {
				acquireMutex();
			}
		}

		private native void acquireMutex();

		@Override
		public void unlock() {
			if (mutex != 0) {
				releaseMutex();
			}
		}

		private native void releaseMutex();

	}

	@Override
	public Process getNextProcess() {
		return null;
	}

	@Override
	public void wait(Object target) {
		waitOnCondition(target);
	}

	private static native void waitOnCondition(Object target);

	@Override
	public void notify(Object target) {
		notifyOnCondition(target);
	}
	
	@Override
	public void notifyAll(Object target)
	{
		
	}
	
	private static native void notifyOnCondition(Object target);

	@Override
	public Monitor getDefaultMonitor() {
		return new JavaLangThreadMonitor();
	}
}
