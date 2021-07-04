package util;

import icecaptools.IcecapCompileMe;

public class ReferenceList {

	private int[] refs;
	private short top;
	public ReferenceList()
	{
		refs = new int[2]; 
		top = 0;
	}

	@IcecapCompileMe
	public void add(int ref) {
		if (top < refs.length)
		{
			refs[top] = ref;
			top++;
		}
		else
		{
			int[] newRefs = new int[refs.length << 1];
			for (short i = 0; i < top; i++)
			{
				newRefs[i] = refs[i];
			}
			refs = newRefs;
			add(ref);
		}
	}

	public void clear() {
		top = 0;
	}

	public boolean isEmpty() {
		return top == 0;
	}

	public int removeLast() {
		top--;
		return refs[top];
	}

	private static class ReferenceIteratorImpl implements ReferenceIterator
	{
		private int[] refs;
		private short top;
		private short index;
		
		ReferenceIteratorImpl(int[] refs, short top)
		{
			this.refs = refs;
			this.top = top;
			this.index = 0;
		}
		
		@Override
		public boolean hasNext() {
			return index < top;
		}

		@Override
		public int next() {
			int n = refs[index];
			index++;
			return n;
		}
	}
	
	public ReferenceIterator iterator() {
		return new ReferenceIteratorImpl(refs, top);
	}

	public int getLast() {
		return refs[top - 1];
	}
}
