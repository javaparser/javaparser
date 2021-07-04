/**************************************************************************
 * File name  : MemoryArea.java
 * 
 * This file is part a SCJ Level 0 and Level 1 implementation, 
 * based on SCJ Draft, Version 0.94 25 June 2013.
 *
 * It is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as  
 * published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 * This SCJ Level 0 and Level 1 implementation is distributed in the hope 
 * that it will be useful, but WITHOUT ANY WARRANTY; without even the  
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this SCJ Level 0 and Level 1 implementation.  
 * If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright 2012 
 * @authors  Anders P. Ravn, Aalborg University, DK
 *           Stephan E. Korsholm and Hans S&oslash;ndergaard, 
 *             VIA University College, DK
 *************************************************************************/

package javax.realtime;

import icecaptools.IcecapCompileMe;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

import reflect.ObjectInfo;
import vm.Memory;

/**
 * All allocation contexts are implemented by memory areas. This is the
 * base-level class for all memory areas.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */

@SCJAllowed(Level.INFRASTRUCTURE)
public abstract class MemoryArea extends Object {
	
	/* The global over all backing store area. This is the root area of 
	 * all other areas. It does not have a provider. 
	 */ 
	public static MemoryArea overAllBackingStore;

	// -------------------------------------------------------------------
	// Backing store for this memory area:
	
	/* The MemoryArea providing the backing store for this MemoryArea */
	protected MemoryArea backingStoreProvider;

	/* The head of a linked list of MemoryAreas contained in this MemoryArea (provided by this MemoryArea) */
	private MemoryArea headOfContainedMemories;  	
	private MemoryArea nextContainedMemory;

	// -------------------------------------------------------------------
	// Allocation area:
	
	protected Memory delegate;

	private int reservedEnd;

	private int maxUsage;
	
	/**
	 * Dummy constructor for javax.realtime.ImmortalMemory
	 */
	protected MemoryArea() {
	}

	/**
	 * Dummy constructor for javax.safetycritical.ManagedMemory.BackingStore
	 */
	protected MemoryArea(Memory delegate) {
		this.delegate = delegate;
		reservedEnd = delegate.getBase() + delegate.getSize();
		delegate.resize(0);
	}

	/**
	 * Creates a new memory area.
	 * 
	 * @param initialSize
	 *    The initial size of this new memory area
	 * 
	 * @param reservedSize
	 *    The size of the reserved area in the backing store in which this memory area is located. This must be 
	 *    larger than or the same as the initialSize  
	 */
//	/*@ 
//	  behavior    
//	    requires size > 0;   
//	    ensures size() == size && memoryConsumed() == 0;
//	@*/

	@IcecapCompileMe
	protected MemoryArea(int initialSize, int reservedSize, MemoryArea backingStoreProvider, String label) {
		int base = backingStoreProvider.reservedEnd - backingStoreProvider.getRemainingBackingstoreSize();

		int endOfAvailableSpace = backingStoreProvider.reservedEnd;

		if (base + reservedSize <= endOfAvailableSpace) {
			this.backingStoreProvider = backingStoreProvider;
			delegate = new Memory(base, initialSize, label);			
			reservedEnd = base + reservedSize;
			backingStoreProvider.addContainedMemory(this);
		} else {
			System.out.println("   MemoryArea: throw " + label);
			throw new OutOfMemoryError("thrown from MemoryArea :: constructor : Out of backingstore exception: size: "
					+ initialSize + " backingStoreSize: " + reservedSize + " base: " + base + " backingStoreEnd: "
					+ endOfAvailableSpace);
		}
	}
	
	private void addContainedMemory(MemoryArea memoryArea) {
		memoryArea.nextContainedMemory = headOfContainedMemories;
		headOfContainedMemories = memoryArea;
		if (memoryArea.reservedEnd > maxUsage)
		{
			maxUsage = memoryArea.reservedEnd;
		}
	}

	private void removeContainedMemory(MemoryArea memoryArea) {
		if (headOfContainedMemories == memoryArea) {
			headOfContainedMemories = headOfContainedMemories.nextContainedMemory;
		} else {
			MemoryArea current = headOfContainedMemories;

			while (current.nextContainedMemory != null) {
				if (current.nextContainedMemory == memoryArea) {
					current.nextContainedMemory = current.nextContainedMemory.nextContainedMemory;
					return;
				}
				current = current.nextContainedMemory;
			}
		}
	}

	/**
	 * Removes <code>this</code> area from the open list with head <code>head</code>.
	 * The head is ImmortalMemory and is never removed.
	 */
	protected void removeMemArea() {
		if (this != overAllBackingStore) {
			backingStoreProvider.removeContainedMemory(this);
		}
	}

	/**
	 * @return The memory consumed (in bytes) in this memory area.
	 */
	@SCJAllowed
	public long memoryConsumed() {
		return (long) delegate.consumedMemory();
	}

	/**
	 * @return The memory remaining (in bytes) in this memory area.
	 */
	@SCJAllowed
	public long memoryRemaining() {
		return size() - memoryConsumed();
	}

	/**
	 * @return The size of the current memory area in bytes.
	 */
	@SCJAllowed
	public long size() {
		return this.delegate.getSize();
	}

	protected void resizeMemArea(long newSize) {

		if (memoryConsumed() < newSize) {
			if (this.delegate.getBase() + newSize < reservedEnd) {
				if (headOfContainedMemories == null) {
					delegate.resize((int) newSize);
					return;
				}
			}
		}
		throw new OutOfMemoryError("thrown from MemoryArea :: resizeMem : Out of backingstore exception ");
	}

	/**
	 * get the overall remaining backing store size.
	 * 
	 * @return the overall remaining backing store size.
	 */
	// Not public in SCJ
	public static int getRemainingMemorySize() {
		return overAllBackingStore.getRemainingBackingstoreSize();
	}

	// Not public in SCJ
	public int getRemainingBackingstoreSize() {
		int maxEnd = delegate.getBase() + delegate.getSize();
		MemoryArea current = headOfContainedMemories;
		while (current != null) {
			maxEnd = maxEnd > current.reservedEnd ? maxEnd : current.reservedEnd;
			current = current.nextContainedMemory;
		}
		return reservedEnd - maxEnd;
	}

	@Override
	public String toString() {
		return delegate.toString();
	}

	// for test purpose
	public static void printMemoryAreas() {
		print(overAllBackingStore, 0);
	}

	protected static MemoryArea getNamedMemoryArea(String name) {
		return getNamedMemoryArea(overAllBackingStore, name);
	}

	private static MemoryArea getNamedMemoryArea(MemoryArea provider, String name) {
		if (provider.delegate.getName().equals(name))
		{
			return provider;
		}
		MemoryArea current = provider.headOfContainedMemories;
		while (current != null)
		{
			MemoryArea result = getNamedMemoryArea(current, name);
			if (result != null)
			{
				return result;
			}
			current = current.nextContainedMemory;
		}
		return null;
	}
	
	/**
	 * @param object An object.
	 * @return The memory area in which <code>object</code> is allocated.
	 */
	@SCJAllowed
	public static MemoryArea getMemoryArea(Object object) {
		int ref = ObjectInfo.getAddress(object);
		
		return getMemoryArea(overAllBackingStore, ref); 
	}
	
	private static MemoryArea getMemoryArea(MemoryArea provider, int ref) {
		
		if ((provider.delegate.getBase() <= ref) && (ref < provider.delegate.getBase() + provider.delegate.getSize()))
		{
			return provider;
		}
		MemoryArea current = provider.headOfContainedMemories;
		while (current != null)
		{
			MemoryArea result = getMemoryArea(current, ref);
			
			if (result != null)
			{
				//System.out.println("MemoryArea.result: " + result);
				return result;
			}
			current = current.nextContainedMemory;
		}
		return null;
	}
	
	
	protected static MemoryArea getCurrentMemoryArea()
	{
		vm.Memory mem = vm.Memory.getCurrentMemoryArea();
		
		return getCurrentMemoryArea (overAllBackingStore, mem);
	}
	
	static MemoryArea getCurrentMemoryArea (MemoryArea provider, Memory mem)
	{
		if (provider.delegate == mem)
		{
			return provider;
		}
		MemoryArea current = provider.headOfContainedMemories;
		while (current != null)
		{
			MemoryArea result = getCurrentMemoryArea(current, mem);
			if (result != null)
			{
				return result;
			}
			current = current.nextContainedMemory;
		}
		return null;
	}
	
	private static void print(MemoryArea backingStoreProvider, int indent) {
		MemoryArea current = backingStoreProvider.headOfContainedMemories;

		int count = indent;
		while (count > 0) {
			devices.Console.print("   ");
			count--;
		}

		int bsstart = backingStoreProvider.delegate.getBase() + backingStoreProvider.delegate.getSize();
		
		devices.Console.print(backingStoreProvider.delegate.getName() + "[used " + backingStoreProvider.delegate.consumedMemory()
				+ " of " + backingStoreProvider.delegate.getSize());
		
		int bssize = backingStoreProvider.reservedEnd - bsstart;

		if (bssize > 0)
		{
			int consumedBackingStore;
			if (backingStoreProvider.maxUsage > 0)
			{
				consumedBackingStore = backingStoreProvider.maxUsage - bsstart;
			}
			else
			{
				consumedBackingStore = 0;
			}
			
			devices.Console.println(", used " + consumedBackingStore + " of " + bssize + "]");
		}
		else
		{
			devices.Console.println("]");
		}

		while (current != null) {
			print(current, indent + 1);
			current = current.nextContainedMemory;
		}
	}

}
