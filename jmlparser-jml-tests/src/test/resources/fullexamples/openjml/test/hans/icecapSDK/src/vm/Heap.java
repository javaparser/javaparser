package vm;

import gc.BitMap;
import util.ReferenceIterator;

public interface Heap {
	/*
	 * @return the block size of the heap in int/words
	 */
	public int getBlockSize();
	
	/*
	 * @return start address of the heap in int/words
	 */
	public int getStartAddress();
	
	/*
	 * @return the size of the heap in int/words
	 */
	public int getHeapSize();
	
	/*
	 * @return amount of available memory in percent of total memory
	 * 
	 */
	public int getMemoryLeftInProcent();
	
	/*
	 * @return all references contained by static variables as an Iterator 
	 * 
	 */
	public ReferenceIterator getStaticRef();
	
	/*
	 * @return all stack cells as an Iterator
	 * 
	 */
	public ReferenceIterator getRefFromStacks();
	
	/*
	 * @param ref A stack cell that might be a reference  
	 * 
	 * @return true if ref is pointing to something that might be an object otherwise false 
	 * 
	 */
	public boolean isRefAnObj(int ref);
	
	/*
	 * @param ref A stack cell that might be a reference  
	 * 
	 * @return true if the object ref is pointing to is allocated otherwise false 
	 * 
	 */
	public boolean isRefAllocated(int ref); 
	
	/*
	 * @param ref A value that might be a reference  
	 * 
	 * @return all references contained by the object pointed to by ref as an Iterator of Integer objects  
	 * 
	 */
	public ReferenceIterator getRefFromObj(int ref);

	void setBitMap(BitMap bitMap);
}
