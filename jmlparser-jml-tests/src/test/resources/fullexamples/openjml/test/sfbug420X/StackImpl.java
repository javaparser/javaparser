package stack;

public class StackImpl implements Stack {
		
	/*@ spec_public */ private int maxSize = 50;
	/*@ spec_public */ private int[] internalStack;
	/*@ spec_public */ private int stackCounter; //@ in count;
	//@ public represents count = stackCounter;
	//@ public invariant stackCounter <= internalStack.length;
	//@ public invariant internalStack.length >= maxSize;
	
	//@ ensures count == 0;
	//@ ensures stackCounter == 0;
	//@ ensures count() == 0;
	@SuppressWarnings("unchecked")
	public StackImpl() {
		internalStack = new int[maxSize];
		stackCounter = 0;
	}
	
	//@ also ensures \result == stackCounter;
	//@ pure
	//@ helper
	public int count() {
		return stackCounter;
	}

	//@ also requires 1 <= i && i <= count();
    //@ ensures \result == internalStack[i-1];
	//@ pure
	public int itemAt(int i) {
		return internalStack[i-1];
	}

	//@ pure
	public boolean isEmpty() {
		return stackCounter == 0;
	}

	public boolean push(int item) {
		if(stackCounter + 1 > maxSize) return false;
		internalStack[stackCounter] = item;
		stackCounter++;
		return true;
	}

	public int top() {
		return internalStack[stackCounter-1];
	}

	public boolean remove() {
		if(stackCounter == 0) return false;
				stackCounter--;
		return true;
	}
	
	public static void main(String[] args) {
		Stack s = new StackImpl();
		//@ assert s.count == 0;
		boolean b1 = s.push(2);
		boolean b2 = s.push(2);
		boolean b3 = s.push(2);
		if (!(b1 && b2 && b3)) return;
		//@ assert s.count() == 3;
		//@ assert s.count == 3;
		System.out.println(s.itemAt(1));
		System.out.println(s.itemAt(2));
		System.out.println(s.itemAt(3));
	}

	public static void main1(String[] args) {
		StackImpl s = new StackImpl();
		//@ assert s.count == 0;
		boolean b1 = s.push(2);
		boolean b2 = s.push(2);
		boolean b3 = s.push(2);
		if (!(b1 && b2 && b3)) return;
		//@ assert s.count() == 3;
		//@ assert s.count == 3;
		//@ assert s.stackCounter == 3;
		System.out.println(s.itemAt(1));
		System.out.println(s.itemAt(2));
		System.out.println(s.itemAt(3));
	}

}
