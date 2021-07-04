/**************************************************************************
 * File name  : ManagedMemory.java
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

package javax.safetycritical;

import icecaptools.IcecapCompileMe;

import javax.realtime.MemoryArea;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

import vm.Memory;

/**
 * Managed memory is a scoped memory area that is managed by a mission.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 */
@SCJAllowed
public abstract class ManagedMemory extends MemoryArea {

	static boolean flag = true;

	/**
	 * statically allocated Exception prevents memory area reference mismatches.
	 */
	private static final IllegalArgumentException exception = new IllegalArgumentException();
	
	private static class BackingStore extends MemoryArea {

		public BackingStore(Memory delegate) {
			super(delegate);
		}
	}

	/**
	 * This method is called once in javax.safetycritical.Launcher
	 * 
	 * @param size
	 *            The size of the backing store used by the SCJ application
	 */
	static void allocateBackingStore(int size) {
		MemoryArea.overAllBackingStore = new BackingStore(Memory.allocateInHeap(size));
	}

	public static class ImmortalMemory extends ManagedMemory // HSO: not public
	{
		ImmortalMemory(int sizeOfArea) {
			super(sizeOfArea, sizeOfArea, MemoryArea.overAllBackingStore, "Imm");
		}

		public static ImmortalMemory instance() {
			MemoryArea result = MemoryArea.getNamedMemoryArea("Imm");
			if (result != null)
			{
				return (ImmortalMemory)result;
			}
			return null;
		}
	}

	/**
	 * @param size  is the number of free bytes in the memory area
	 */
	@IcecapCompileMe
	ManagedMemory(int size, int BackingStoreOfThisMemory, 
			      MemoryArea backingStoreProvider, String label) {
		super(size, BackingStoreOfThisMemory, backingStoreProvider, label);
	}

	/**
	 * Makes this memory area the allocation context for the execution of the
	 * <code>run()</code> method of the instance of <code>Runnable</code> given
	 * in the constructor. <br>
	 * During this period of execution, this memory area becomes the default
	 * allocation context until another allocation context is selected or the
	 * <code>Runnable</code>'s <code>run</code> method exits.
	 * <p>
	 * This method is like the <code>executeInArea</code> method, but extended
	 * with cleanup and pointer reset.
	 * 
	 * @throws IllegalArgumentException
	 *    if the caller is a schedulable object and <code>logic</code>
	 *    is null.
	 * 
	 * @param logic
	 *    is the <code>Runnable</code> object whose <code>run()</code>
	 *    method shall be executed.
	 */
	@SCJAllowed(Level.INFRASTRUCTURE)
	@IcecapCompileMe
	void enter(Runnable logic) throws IllegalArgumentException {
		if (logic == null || !( logic instanceof ManagedSchedulable)) 
			throw new IllegalArgumentException(); 
		
		ManagedSchedulable ms = (ManagedSchedulable) logic;
		
		if (ms instanceof ManagedEventHandler) {
			ManagedEventHandler mevh = (ManagedEventHandler) ms;
			Memory mem = Memory.switchToArea(mevh.privateMemory.delegate);
			logic.run();
			Memory.switchToArea(mem);
			mevh.privateMemory.delegate.reset(0);
		}
		else if (ms instanceof ManagedThread) {
			devices.Console.println("ManagedMemory.enter: managedThred should work");
			ManagedThread mth = (ManagedThread) ms;
			Memory mem = Memory.switchToArea(mth.privateMemory.delegate);
			logic.run();
			Memory.switchToArea(mem);
			mth.privateMemory.delegate.reset(0);			
		}
		else { 
			// (ms is instanceof ManagedLongEventHandler)
			devices.Console.println("ManagedMemory.enter: UPS ManagedLongEventHandler not implemented");
			//ManagedLongEventHandler mevh = (ManagedLongEventHandler) ms;
			// finish this ...
		}
	}
	
	/**
	 * Executes <code>logic</code> in this memory area, with no cleanup and no
	 * pointer reset at the end.
	 * 
	 * @param logic
	 *    The Runnable object whose <code>run()</code> method shall be executed.
	 * 
	 * @throws IllegalArgumentException
	 *    If <code>logic</code> is null.
	 */
	@SCJAllowed
	void executeInArea(Runnable logic) throws IllegalArgumentException {
		if (logic == null)
			throw new IllegalArgumentException("executeInArea: logic is null");

		if (flag) {
			flag = false;
			Memory currentMem = vm.Memory.getHeapArea();
			Memory.switchToArea(this.delegate);
			logic.run();
			Memory.switchToArea(currentMem);
		} 
		else {						
			ScjProcess currProcess = getCurrentProcess();
			if (currProcess == null)
				throw new IllegalArgumentException("executeInArea: process is null");
			
			Memory mem = Memory.switchToArea(this.delegate);
			logic.run();
			Memory.switchToArea(mem);
		}		
	}

	static final ManagedMemory getOuterMemory(MemoryArea mem) {
		if (mem instanceof InnerPrivateMemory)
			return ((InnerPrivateMemory) mem).prev;
		
		else if (mem instanceof PrivateMemory)
			return Mission.getMission().getSequencer().getMissionMemory();
		
		else if (mem instanceof MissionMemory)
		{
			// return nearest outermost memory
			MissionSequencer<?> missSeq = Mission.getMission().getSequencer();
			if (missSeq.outerSeq == null)
				return ImmortalMemory.instance();
			else
				return missSeq.getOuterSeq().getMissionMemory();
		}
		else 	
			return null;
	}

	/**
	 * Invoke the run method of logic with a fresh private memory area that is
	 * immediately nested within the current <code>ManagedMemory</code> area,
	 * sized to provide <code>size</code> bytes of free memory as the current
	 * allocation area.
	 * 
	 * @param size
	 *            is the number of free bytes within the inner-nested private
	 *            memory.
	 * 
	 * @param logic
	 *            provides the run method that is to be executed within the
	 *            inner-nested private memory area.
	 */
//	/*@ 
//	  public static normal_behavior
//	    requires logic != null;	 
//	    ensures true;  // not finished
//	  also
//	  public static exceptional_behaviour
//	    requires logic == null; 
//	    signals (IllegalStateException) true;
//	  
//	  @*/
	@SCJAllowed
	public static void enterPrivateMemory(int size, Runnable logic) throws IllegalStateException {
		/**
		 * prevMemory is the memory area at entry; prevFree is the free pointer
		 * before allocation of the private memory. If the current free has
		 * changed after running the logic, there has been allocation in the
		 * outer area, and the private memory cannot be released.
		 */
		if (logic == null)
			throw exception;
		
		vm.ClockInterruptHandler.instance.disable();  // atomic operation ??
		
		ManagedSchedulable ms = getCurrentProcess().getTarget();
		//devices.Console.println("enterPrivateMemory by " + getCurrentProcess().index);
		runEnterPrivateMemory(ms, size, logic);
		
		vm.ClockInterruptHandler.instance.enable();
	}

	private static void  runEnterPrivateMemory(ManagedSchedulable ms, int size, Runnable logic)
	{
		ManagedMemory prev = getMemory (ms);
		long prevFree = prev.memoryConsumed();

		InnerPrivateMemory inner = 
			new InnerPrivateMemory(
					size, prev.getRemainingBackingstoreSize(), prev,
					"InnerPrvMem");
		inner.prev = prev;

		Memory mem = Memory.switchToArea(inner.delegate);
		logic.run();
		Memory.switchToArea(mem); 

		if (prev.memoryConsumed() != prevFree)
			prev.resetArea(prevFree);

		inner.removeArea();
	}
		
	private static ManagedMemory getMemory (ManagedSchedulable ms)
	{
		if (ms instanceof ManagedEventHandler) {
			ManagedEventHandler mevh = (ManagedEventHandler) ms;
			return mevh.privateMemory; 
		}
		else if(ms instanceof ManagedThread) {
			ManagedThread mth = (ManagedThread) ms;
			return mth.privateMemory; 
		}
		else  {
			// (ms is instanceof ManagedLongEventHandler)
			ManagedLongEventHandler mlevh = (ManagedLongEventHandler) ms;
			return mlevh.privateMemory;
		}
	}
	
	@SCJAllowed
	public static void executeInAreaOf(Object obj, Runnable logic) {
		if (obj == null || logic == null)
			throw exception;
		
		vm.ClockInterruptHandler.instance.disable();  // atomic operation ??
		
		ManagedMemory memAreaOfObject = (ManagedMemory)MemoryArea.getMemoryArea(obj);
		//devices.Console.println("executeInAreaOf: memAreaOfObject: " + memAreaOfObject);
		
		Memory mem = Memory.switchToArea(memAreaOfObject.getDelegate());
		logic.run();
		Memory.switchToArea(mem);
		
		vm.ClockInterruptHandler.instance.enable();  // atomic operation ??
	}

	@SCJAllowed
	public static void executeInOuterArea(Runnable logic) {
		if (logic == null)
			throw exception;

		vm.ClockInterruptHandler.instance.disable();  // atomic operation ??
		
		MemoryArea currentMem = MemoryArea.getCurrentMemoryArea();
		//devices.Console.println("executeInOuterArea: currentMem: " + currentMem);
		
		if (currentMem instanceof ManagedMemory.ImmortalMemory) {
			devices.Console.println("executeInOuterArea: already in ImmortalMemory");
			
			vm.ClockInterruptHandler.instance.enable();  // atomic operation ??
			throw new IllegalStateException("executeInOuterArea: already in ImmortalMemory");		
		}				
		
		ManagedMemory outerMemory = getOuterMemory(currentMem);		
		
		Memory mem = Memory.switchToArea(outerMemory.getDelegate());
		logic.run();
		Memory.switchToArea(mem);
		
		vm.ClockInterruptHandler.instance.enable();  // atomic operation ??
	}

	/**
	 * 
	 * @return the size of the remaining memory available to the current
	 *         ManagedMemory area.
	 * @scjComment the same as memoryRemaining() in MemoryArea?
	 */
	@SCJAllowed
	public long getRemainingBackingStore() {
		return memoryRemaining();
	}

	/**
	 * Resetting the number of available bytes. The parameter
	 * <code>newFree</code> is typically acquired by a previous call of
	 * <code>memoryConsumed()</code>.
	 * 
	 * @param newFree
	 *            the number.
	 */
	private void resetArea(long newFree) {
		this.delegate.reset((int) newFree);
	}

	void resetArea() {
		this.delegate.reset(0);
	}

	void removeArea() {
		this.removeMemArea();
	}
	
	void resizeArea(long newSize) {
		this.resizeMemArea(newSize);

	}

	static ScjProcess getCurrentProcess() {
		if (Launcher.level != 0)
			return PriorityScheduler.instance().getCurrentProcess();
		else
			return CyclicScheduler.instance().getCurrentProcess();
	}

	protected Memory getDelegate() {
		return delegate;
	}
	
	
	// For JML annotations
	/*@ spec_public @*/ static MemoryArea getCurretAllocationArea()
	{
		return null;
	}
	
	// For JML annotations
	/*@ spec_public @*/  MemoryArea getTopMostArea()
	{
		return null;
	}
	
}
