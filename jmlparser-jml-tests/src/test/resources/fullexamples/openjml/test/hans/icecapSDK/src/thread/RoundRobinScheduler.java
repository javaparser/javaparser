package thread;

import vm.Monitor;
import vm.Process;
import vm.Scheduler;

public class RoundRobinScheduler extends ThreadManager implements Scheduler {

	private static final int DEFAULT_SEQUENCER_STACK_SIZE = 1024;

	private boolean started;
	
	private int index;

	private vm.ClockInterruptHandler clockHandler;

	private Thread thr;
	
	public RoundRobinScheduler() {
		super();
		started = false;		
		index = 0;
	}

	@Override
	public Process getNextProcess() {
		while (true) {
			thr = threads.get(index);
			index++;
			if (index >= threads.size())
			{
				index = 0;
			}
			if (thr.state != Thread.FINISHED)
			{
				return thr.p;
			}
		}
	}

	public void start() {
		if (!started) {
			int[] sequencerStack = new int[DEFAULT_SEQUENCER_STACK_SIZE];

			vm.ClockInterruptHandler.initialize(this, sequencerStack);
			clockHandler = vm.ClockInterruptHandler.instance;

			Thread mainThread = new Thread(new vm.Process(null, null));
			mainThread.state = Thread.RUNNING;
			threads.add(mainThread);
			clockHandler.register();
			clockHandler.startClockHandler(mainThread.p);
			started = true;
			clockHandler.enable();
			clockHandler.yield();
		}
	}

	public void addThread(Thread thread) {
		clockHandler.disable();
		threads.add(thread);
		clockHandler.enable();
	}

	public Thread currentThread() {
		return thr;
	}

	public void removeThread(Thread thread) {
		clockHandler.disable();
		threads.remove(thread);
		clockHandler.enable();
	}

	@Override
	public void disable() {
		clockHandler.disable();
	}

	@Override
	public void enable() {
		clockHandler.enable();
	}

	@Override
	public void wait(Object target) {

	}

	@Override
	public void notify(Object target) {
		
	}
	
	@Override
	public void notifyAll(Object target) {
		
	}
	@Override
	public Monitor getDefaultMonitor() {
		return null;
	}

}
