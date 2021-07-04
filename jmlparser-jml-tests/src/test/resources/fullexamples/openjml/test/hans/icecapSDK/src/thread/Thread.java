package thread;

import vm.Process;

public class Thread implements Runnable {
	private static final int DEFAULT_THREAD_STACK_SIZE = 1024;

	static final byte FINISHED = 1;
	static final byte RUNNING = 2;

	private static RoundRobinScheduler scheduler;

	Process p;
	byte state;

	public Thread(final Runnable logic) {
		initialize(logic);
	}

	protected void initialize(final Runnable logic) {
		if (scheduler == null) {
			scheduler = new RoundRobinScheduler();
		}

		state = RUNNING;
		p = new vm.Process(new vm.ProcessLogic() {
			@Override
			public void run() {
				logic.run();
				state = FINISHED;
			}

			@Override
			public void catchError(Throwable t) {
				devices.Console.println("Thread: exception -> " + t);
			}

		}, new int[DEFAULT_THREAD_STACK_SIZE]);
		p.initialize();
	}

	public Thread() {
		initialize(this);
	}

	Thread(Process process) {
		this.p = process;
	}

	public void start() {
		scheduler.start();
		scheduler.addThread(this);
	}

	public void join() throws InterruptedException {
		while (state == RUNNING) {
			;
		}
		//scheduler.removeThread(this); Does not work and this is an error
	}

	@Override
	public void run() {
	}

	public static ThreadManager getScheduler() {
		return scheduler;
	}

	public static Thread currentThread() {
		return scheduler.currentThread();
	}

	public int[] getStack() {
		return p.getStack();
	}

	public short getJavaStackTop() {
		return p.getJavaStackTop();
	}

	public int getCStackTop() {
		return p.getCStackTop();
	}

	public static void sleep(int ms) throws InterruptedException {
		;
	}

	public static void print(String string) {
		scheduler.disable();
		devices.Console.println(string);
		scheduler.enable();
	}

}
