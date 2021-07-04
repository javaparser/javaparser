package vm;

public interface Scheduler {
	public vm.Process getNextProcess();

	void wait(Object target);

	void notify(Object target);
	
	void notifyAll(Object target);

	public Monitor getDefaultMonitor();

	/* TODO: void terminated(); */
}
