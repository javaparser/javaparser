package vm;

import gc.BitMap;
import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;

import java.util.Iterator;

import reflect.ClassInfo;
import reflect.ObjectInfo;
import reflect.StaticRefInfo;
import thread.Thread;
import thread.ThreadManager;
import util.ReferenceIterator;

public class HVMHeap implements Heap {

	@IcecapCVar
	private static int java_heap_size;

	private EmptyIterator emptyIterator;
	private ObjectReferenceIterator objectReferenceIterator;
	private ObjectInfo oi;

	private BitMap bitMap;

	private int blockSize;

	private int startAddress;

	private int heapSize;

	public HVMHeap() {
		emptyIterator = new EmptyIterator();
		oi = new ObjectInfo();

		blockSize = _getBlockSize();

		startAddress = _getStartAddress();

		heapSize = _getHeapSize();

		objectReferenceIterator = new ObjectReferenceIterator(this);
	}

	public static Heap getHeap() {
		return new HVMHeap();
	}

	@Override
	public int getMemoryLeftInProcent() {
		return 100;
	}

	private void unimplemented(String from) {
		Thread.print(from);
		while (true)
			;
	}

	private static class EmptyIterator implements ReferenceIterator {
		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public int next() {
			return -1;
		}
	}

	private static class StaticReferenceIterator implements ReferenceIterator {
		private int[] offsets;
		private short top;

		public StaticReferenceIterator(int[] offsets) {
			this.offsets = offsets;
			top = 0;
		}

		@Override
		public boolean hasNext() {
			return top < offsets.length;
		}

		@Override
		public int next() {
			int ref = StaticRefInfo.getReference(offsets[top]);
			top++;
			return ref;
		}
	}

	@Override
	public ReferenceIterator getStaticRef() {
		int[] offsets = StaticRefInfo.getOffsets();
		return new StaticReferenceIterator(offsets);
	}

	private static class ThreadIterator {
		private Iterator<Thread> threads;
		private Thread nextThread;

		public ThreadIterator() {
			ThreadManager manager = Thread.getScheduler();
			threads = manager.getThreads();
			advance();
		}

		private void advance() {
			if (threads.hasNext()) {
				Thread current = threads.next();
				if (current != Thread.currentThread()) {
					nextThread = current;
					if (nextThread.getStack() == null) {
						advance();
					}
				} else {
					advance();
				}
			} else {
				nextThread = null;
			}
		}

		public boolean hasNext() {
			return nextThread != null;
		}

		public Thread next() {
			Thread t = nextThread;
			advance();
			return t;
		}
	}

	private static class StackRefIterator implements ReferenceIterator {
		private int[] currentStack;
		private int currentIndex;
		private short top;

		private Thread currentThread;

		ThreadIterator threads;

		public StackRefIterator() {
			threads = new ThreadIterator();
			currentStack = null;
			advance();
		}

		private void advance() {
			if (currentStack == null) {
				if (threads.hasNext()) {
					currentThread = threads.next();
					currentStack = currentThread.getStack();
					currentIndex = 0;
					top = currentThread.getJavaStackTop();
				}
			} else {
				currentIndex++;
				if (currentIndex == top) {
					currentIndex = currentThread.getCStackTop();
				} else if (currentIndex == currentStack.length) {
					currentStack = null;
					advance();
				} else {
				}
			}
		}

		@Override
		public boolean hasNext() {
			return currentStack != null;
		}

		@Override
		@IcecapCompileMe
		public int next() {
			int ref = currentStack[currentIndex];
			advance();
			return ref;
		}

	}

	@Override
	public ReferenceIterator getRefFromStacks() {
		return new StackRefIterator();
	}

	@Override
	public boolean isRefAnObj(int ref) {
		oi.setAddress(ref);

		short classId = oi.classId;

		if (classId >= 0) {
			if (classId < ClassInfo.getNumberOfClasses()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean isRefAllocated(int ref) {
		return true;
	}

	private static class ObjectReferenceIterator implements ReferenceIterator {
		private ReferenceIterator referenceOffsets;
		private ObjectInfo oi;
		private int nextRef;

		private int startAddress;
		private int endAddress;

		ObjectReferenceIterator(Heap heap) {
			this.startAddress = heap.getStartAddress();
			this.endAddress = startAddress + heap.getHeapSize();
		}

		public void initObjectReferenceIterator(ReferenceIterator referenceOffsets, ObjectInfo oi) {
			this.referenceOffsets = referenceOffsets;
			this.oi = oi;
			nextRef = 0;
		}

		@Override
		public boolean hasNext() {
			if (nextRef != 0) {
				return true;
			}
			if (referenceOffsets.hasNext()) {
				nextRef = oi.getRef((short) referenceOffsets.next());
				if ((nextRef >= startAddress) && (nextRef < endAddress)) {
					return true;
				} else {
					return hasNext();
				}
			} else {
				return false;
			}
		}

		@Override
		public int next() {
			int ref = nextRef;
			nextRef = 0;
			return ref;
		}
	}

	@Override
	public ReferenceIterator getRefFromObj(int ref) {
		oi.setAddress(ref);

		short classId = oi.classId;

		if (classId >= 0) {
			if (classId < ClassInfo.getNumberOfClasses()) {
				ClassInfo cInfo = ClassInfo.getClassInfo(classId);
				ReferenceIterator referenceOffsets = cInfo.getReferenceOffsets(ref);
				if (referenceOffsets != null) {
					objectReferenceIterator.initObjectReferenceIterator(referenceOffsets, oi);
					return objectReferenceIterator;
				}
			}
		}
		return emptyIterator;
	}

	private int _getBlockSize() {
		return 4;
	}

	private int _getStartAddress() {
		return getHeapStart();
	}

	private static native int getHeapStart();

	@IcecapCompileMe
	private int _getHeapSize() {
		return java_heap_size;
	}

	@Override
	public void setBitMap(BitMap bitMap) {
		this.bitMap = bitMap;
	}

	@Override
	public int getBlockSize() {
		return blockSize;
	}

	@Override
	public int getStartAddress() {
		return startAddress;
	}

	@Override
	public int getHeapSize() {
		return heapSize;
	}
}
