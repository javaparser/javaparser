/**************************************************************************
 * File name  : ManagedThread.java
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

import javax.realtime.AbsoluteTime;
//import javax.realtime.Clock;
import javax.realtime.HighResolutionTime;
import javax.realtime.MemoryArea;
import javax.realtime.RealtimeThread;
import javax.realtime.PriorityParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;
import javax.safetycritical.annotate.SCJRestricted;

import vm.ClockInterruptHandler;
import vm.Memory;

/**
 * This class enables a mission to keep track of all the no-heap realtime 
 * threads that are created during the initialization phase.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 *
 */
@SCJAllowed(Level.LEVEL_2)
public class ManagedThread extends RealtimeThread implements
		ManagedSchedulable {

	PriorityParameters priority;
	StorageParameters storage;
	ScjProcess process;
	Mission mission = null;

	ManagedMemory privateMemory;
	
	// used in JML spec. methods
	boolean isRegistered;
	boolean isInMissionScope;
	
	public ManagedThread(PriorityParameters priority, StorageParameters storage) {
		this(priority, storage, null);
	}

	public ManagedThread(PriorityParameters priority, StorageParameters storage, Runnable logic) {
		super(priority, logic);
		this.priority = priority;
		
		if (storage == null)
			throw new IllegalArgumentException("storage is null");
		
		this.storage = storage;
		this.mission = Mission.getMission();
		
		int backingStoreOfThisMemory = 
			mission == null ? 
				MemoryArea.getRemainingMemorySize() : 
				(int) this.storage.totalBackingStore;
	    MemoryArea backingStoreProvider = 
			mission == null ? MemoryArea.overAllBackingStore : 
				mission.currMissSeq.missionMemory;
	    
	    String privateMemoryName = Memory.getNextMemoryName("PvtMem");
	    
	    privateMemory = new PrivateMemory((int) storage.getMaxMemoryArea(), 
	    								   backingStoreOfThisMemory, 
	    								   backingStoreProvider,
	    								   privateMemoryName);
	    this.isRegistered = false;
	    this.isInMissionScope = false;
	}	
	
	Mission getMission() {
		return mission;
	}
	
	@SCJAllowed(Level.INFRASTRUCTURE)
	@SCJRestricted(Phase.INITIALIZE)
	public final void register() {
		ManagedSchedulableSet msSet = Mission.getMission().msSetForMission;
		msSet.addMS(this);
		
		isRegistered = true;
		isInMissionScope = true;
	}
	
	@SCJAllowed(Level.SUPPORT)
	@SCJRestricted(Phase.CLEANUP)
	public void cleanUp() {
		privateMemory.removeArea();
	}
	
	public void signalTermination() {		
		//process.state = ScjProcess.State.HANDLED;
		//devices.Console.println("ManagedThread.signalTermination: process " + process.index); // + "; state " + process.state);

//		ManagedSchedulableSet msSet = Mission.getCurrentMission().msSetForMission;
//		msSet.removeMSObject(this);
	}
	
	/**
	 * Remove the currently execution schedulable object from the set of 
	 * runnable schedulable object until time.
	 * 
	 * @param time
	 * @throws java.lang.InterruptedException
	 */
	public static void sleep(HighResolutionTime time) throws java.lang.InterruptedException {
		vm.ClockInterruptHandler.instance.disable();
		// get current process and reset the boolean value
		ScjProcess current = PriorityScheduler.instance().current;
		// get current time.
		//AbsoluteTime abs = Clock.getRealtimeClock().getTime(current.next);
		
		
		// set the next release time for current process
		if (time instanceof RelativeTime) {
			current.next.add((RelativeTime) time, current.next);
			//current.next = abs.add((RelativeTime) time, abs);
		} 
		else if (time instanceof AbsoluteTime) {
			current.next = new AbsoluteTime((AbsoluteTime) time);
		} 
		else {
			throw new UnsupportedOperationException();
		}

		// set state to SLEEPING 
		current.state = ScjProcess.State.SLEEPING;		

		// transfer process; 
		// PriorityScheduler.move() will call gotoNextState that inserts 
		// current process (ScjManagedThreadProcess) in sleeping queue. 
		vm.ClockInterruptHandler.instance.enable();
		ClockInterruptHandler.instance.yield();
	}
}
