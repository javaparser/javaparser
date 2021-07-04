package javax.safetycritical;

/**
 * This class is a two dimension set, which contains pairs of clock and process. 
 * The infrastructure will use this class to model the wait set and lock set.
 */
class PriorityQueueForLockAndWait {
	int[] queue;
	int tail;
	int queueSize;

	PriorityQueueForLockAndWait(int size) {
		queue = new int[size];
		tail = -1;
		queueSize = 0;
		
		makeEmptyQueue(queue);
	}

	private void makeEmptyQueue(int[] set) {
		for (int i = 0; i < set.length; i++)
			set[i] = -999;
	}

	/**
	 * Add a relation between the lock and the process into the set.
	 * 
	 * @param target
	 *            The lock associate with the process
	 * @param process
	 *            The process
	 */
	protected void addProcess(Object monitor, ScjProcess process) {
		vm.ClockInterruptHandler.instance.disable();
		
		if (tail < queue.length - 1) {
			tail++;
			int index = tail;
			// find the place in the set for this process
			for (int i = 0; i < tail; i++) {
				ScjProcess temp = getScjProcess(queue[i]);
				if (temp == null)
					throw new IllegalArgumentException("1");
												
				if (ManagedSchedMethods.getPriorityParameter(process.getTarget()).getPriority() 
						> ManagedSchedMethods.getPriorityParameter(temp.getTarget()).getPriority()) {
					index = i;
					break;
				}
			}
			// reserve the place in the set for this process
			if (index != tail) {
				for (int i = tail; i > index; i--) {
					queue[i] = queue[i - 1];
				}
			}
			// add the index of the process into the set and set the required lock
			process.monitorLock = monitor;
			queue[index] = process.index;
			queueSize++;
		} else {
			throw new IndexOutOfBoundsException("set: too small");
		}
		//print();
		vm.ClockInterruptHandler.instance.enable();
	}

	/**
	 * Get the first process who needs to lock. 
	 * Rules: 
	 * 1. The highest priority process who needs the lock will be returned. 
	 * 2. If there are more than one processes who have the same priority, then FIFO.
	 * 
	 * @param target
	 *            The lock
	 * @return The process who needs to lock.
	 */
	protected /*synchronized*/ ScjProcess getNextProcess(Object monitor) {
		for (int i = 0; i <= tail; i++) {
			ScjProcess process = getScjProcess(queue[i]);
			if (process.monitorLock == monitor) {
				process.monitorLock = null;
				reorderSet(i);
				queueSize--;
				return process;
			}
		}
		return null;
	}

	public /*synchronized*/ void removeProcess(ScjProcess process) {
		for (int i = 0; i <= tail; i++) {
			if (queue[i] == process.index) {
				reorderSet(i);
				process.monitorLock = null;
				
				queueSize--;
			}
		}
	}

	private void reorderSet(int index) {
		for (int i = index; i <= tail - 1; i++) {
			queue[i] = queue[i + 1];
		}
		queue[tail] = -999;
		tail--;
	}

	private ScjProcess getScjProcess(int processIdx) {
		if (processIdx == -999) {
			return null;
		}
		if (processIdx == -2) {
			return PriorityScheduler.instance().outerMostSeqProcess;
		}
		if (processIdx == -1) {
			return ScjProcess.idleProcess;
		}

		int missionIndex = processIdx / 20;
		int scjProcessIndex = processIdx % 20;
		return Mission.getScjProcess(missionIndex, scjProcessIndex);
	}

	/**
	 * For testing purpose.
	 */
	public void print() {
		devices.Console.println("queue size = " + (tail + 1));
//		for (int i = 0; i <= tail; i++) {
//			ScjProcess temp = getScjProcess(queue[i]);
//			if (temp != null)
//				devices.Console.println(temp.print());
//		}

		for (int i = 0; i < queue.length; i++) {
			devices.Console.print("[ " + queue[i] + " ] ");
		}
		devices.Console.println("");
	}
}