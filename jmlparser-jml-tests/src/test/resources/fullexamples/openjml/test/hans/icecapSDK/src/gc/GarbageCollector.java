package gc;

import icecaptools.IcecapCompileMe;
import reflect.ClassInfo;
import reflect.ObjectInfo;
import thread.Semaphore;
import thread.Thread;
import util.LiveSet;
import util.ReferenceIterator;
import vm.HVMHeap;
import vm.Heap;

public class GarbageCollector implements Runnable {
	public boolean GCstopped;

	private static Semaphore gcFinished;
	private static GCMonitor monitor;
	private static Thread gc;

	private static ReferenceIterator staticRoots;
	private static LiveSet liveSet;
	private static BitMap bitMap;
	private static boolean GCIsRunning;
	private static Heap heap;
	private Semaphore startGC;
	private Semaphore endGC;

	static {
		init();
	}

	@IcecapCompileMe
	private static void init() {
		GCIsRunning = false;
		heap = HVMHeap.getHeap();
		bitMap = new BitMap(heap.getBlockSize(), heap.getStartAddress(), heap.getHeapSize());
		heap.setBitMap(bitMap);

		Object hack = new Object();
		newBarrier(ObjectInfo.getAddress(hack));
		writeBarrier(0, 0);

		short count = ClassInfo.getNumberOfClasses();
		do {
			count--;
			ClassInfo.getClassInfo(count);
		} while (count > 0);

	}

	public GarbageCollector(Semaphore startGC, Semaphore endGC) {
		this.startGC = startGC;
		this.endGC = endGC;
		GCstopped = false;
	}

	@IcecapCompileMe
	private static void writeBarrier(int source, int oldRef) {
		if (GCIsRunning) {
			if (Thread.currentThread() != gc) {
				if (!bitMap.isRefBlack(source)) {
					if (oldRef != 0) {
						if (bitMap.isRefWhite(oldRef)) {
							liveSet.push(oldRef);
						}
					}
				}
			}
		}
	}

	@IcecapCompileMe
	private static void newBarrier(int ref) {
		if (GCIsRunning) {
			if (Thread.currentThread() == gc) {
				bitMap.shadeRefWhite(ref);
			} else {
				bitMap.shadeRefBlack(ref);
			}
		} else {
			if (bitMap != null) {
				bitMap.shadeRefWhite(ref);
			}
		}
	}

	private void setRoots() {
		liveSet.clear();
		staticRoots = heap.getStaticRef();
		while (staticRoots.hasNext()) {
			int nextRoot = staticRoots.next();
			if (nextRoot != 0) {
				monitor.addStaticRoot(nextRoot);
				liveSet.push(nextRoot);
			}
		}

		ReferenceIterator stackRoots = heap.getRefFromStacks();
		while (stackRoots.hasNext()) {
			int possibleRef = stackRoots.next();
			if (possibleRef != 0) {
				if (bitMap.isWithinRangeOfHeap(possibleRef)) {
					if (heap.isRefAnObj(possibleRef)) {
						if (heap.isRefAllocated(possibleRef)) {
							liveSet.push(possibleRef);
							monitor.addStackRoot(possibleRef);
						}
					}
				}
			}
		}
	}

	private void traverse(LiveSet nodes) {
		ReferenceIterator children;
		int parent;

		while (!nodes.isEmpty()) {
			parent = nodes.pop();
			children = heap.getRefFromObj(parent);
			while (children.hasNext()) {
				int child = children.next();
				if (child != 0) {
					if (bitMap.isWithinRangeOfHeap(child)) {
						monitor.visitChild(parent, child);
						if (!bitMap.isRefBlack(child)) {
							nodes.push(child);
						}
					}
				}
			}
			bitMap.shadeRefBlack(parent);
		}
	}

	private void makeFreeList() {
		ReferenceIterator freeList = bitMap.getFreeList();
		while (freeList.hasNext()) {
			monitor.freeObject(freeList.next());
		}
	}

	public void run() {
		while (!GCstopped) {

			Thread.print("GC wait for next cycle");
			// run when signaled from controller thread
			startGC.acquire();
			Thread.print("starting GC cycle");

			GCIsRunning = true;

			Thread.getScheduler().disable();
			setRoots();
			Thread.getScheduler().enable();

			// start incremental traversal of object graph
			traverse(liveSet);

			GCIsRunning = false;
			// stops the write and new barrier - if free is not atomic then
			// position and relation regarding the free operation to be
			// considered ...

			// free unused object - atomic ?
			makeFreeList();

			// signal controller that GC is finished
			endGC.release();
			gcFinished.release();
		}
	}

	public static void start() {
		Semaphore startGC = new Semaphore((byte) 0);
		Semaphore endGC = new Semaphore((byte) 0);
		gcFinished = new Semaphore((byte) 0);

		Thread controller = new Thread(new GarbargeCollectorController(startGC, endGC));
		gc = new Thread(new GarbageCollector(startGC, endGC));

		liveSet = new LiveSet(bitMap);

		devices.Console.println("Bitmap size = " + bitMap.getSize());
		controller.start();
		gc.start();

	}

	public static void registerMonitor(GCMonitor m) {
		monitor = m;
	}

	public static void requestCollection() {
		GarbargeCollectorController.requestCollection();
	}

	public static void waitForNextCollection() {
		gcFinished.acquire();
	}
}
