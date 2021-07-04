package thread;

import java.util.ArrayList;
import java.util.Iterator;

public abstract class ThreadManager {

	protected ArrayList<Thread> threads;

	protected ThreadManager() {
		threads = new ArrayList<Thread>();
	}

	public Iterator<Thread> getThreads() {
		return threads.iterator();
	}
	
	public abstract void disable();
	
	public abstract void enable();
}
