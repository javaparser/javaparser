package gc;

// test
import thread.Semaphore;
import thread.Thread;

import vm.HVMHeap;
import vm.Heap;

public class GarbargeCollectorController implements Runnable {

	private Heap heap;
	private Semaphore startGC;
	private Semaphore endGC;
	private static boolean requestGC;

	public boolean GCCStopped;

	public GarbargeCollectorController(Semaphore startGC, Semaphore endGC) {
		heap = HVMHeap.getHeap();
		this.startGC = startGC;
		this.endGC = endGC;
		GCCStopped = false;
	}

	// GC controller thread
	public void run() {
		while (!GCCStopped) {
			// check level of free memory

			if ((heap.getMemoryLeftInProcent() < 50) || requestGC) {
				// Start GC thread if memory is too low
				requestGC = false;
				startGC.release();
				// waiting for GC thread to finish its job
				// future improvement: dynamically increase priority of gc thread if memory level becomes too low
				// (then no bilateral semaphore rendezvous but constant checking)  
				endGC.acquire();
			}

			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			} 
		}
	}

	public static void requestCollection() {
		requestGC = true;
	}
	
}
