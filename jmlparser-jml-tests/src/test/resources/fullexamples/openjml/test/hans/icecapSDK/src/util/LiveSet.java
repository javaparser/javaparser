package util;

import gc.BitMap;


public class LiveSet extends ReferenceList {

	private BitMap bm; 
	
	public LiveSet(BitMap bm)
	{
		this.bm = bm;
	}
	
	public void push(int ref) {
		bm.shadeRefGrey(ref);
		super.add(ref);
	}

	public int pop() {
		return super.removeLast();
	}
}
