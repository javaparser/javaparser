/**************************************************************************
 * File name  : ManagedEventHandler.java
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
import javax.realtime.BoundAsyncEventHandler;
import javax.realtime.MemoryArea;
import javax.realtime.PriorityParameters;
import javax.realtime.ReleaseParameters;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;
import javax.safetycritical.annotate.SCJRestricted;

import vm.Memory;

/**
 * <code>ManagedEventHandler</code> is the base class for all SCJ handlers.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment - SCJ issue: In constructor, null arguments for priority and
 *             release parameters are left for resolution by infrastructure
 *             initialization <br>
 *             - SCJ issue: In constructor, if storage parameter is null, 
 *             a default value is given. <br>
            
 */
@SCJAllowed
public abstract class ManagedEventHandler extends BoundAsyncEventHandler implements ManagedSchedulable {

	PriorityParameters priority;
	StorageParameters storage;
	ScjProcess process;
	Mission mission = null;
	
	ManagedMemory privateMemory;
	
	ReleaseParameters release;

	String name;
	
	// used in JML spec. methods
	boolean isRegistered;
	boolean isInMissionScope;

	/**
	 * Constructs an event handler.
	 * 
	 * @param priority specifies the priority parameters.
	 * @param release  specifies the release parameters.
	 * @param storage  specifies the non-null maximum storage demands for this event handler.
	 * 
	 * @throws <code>IllegalArgumentException</code> if priority or release parameters are null.
	 */
	/*@ 
	  public normal_behavior      
	    requires priority != null;
	    requires release != null;  
	
//	    ensures this.getPriorityParam().getPriority() == priority.getPriority();  
//	    ensures this.getReleaseParam().getDeadline() == release.getDeadline();
//	    ensures this.getReleaseParam().getMissHandler() == release.getMissHandler();
	
	  also
	  public exceptional_behavior
	    requires priority == null;
	    signals (IllegalArgumentException) true;
	  also
	  public exceptional_behavior
	    requires release == null;
	    signals (IllegalArgumentException) true;        
	  @*/
	public ManagedEventHandler(PriorityParameters priority, ReleaseParameters release, StorageParameters storage) {
		if (priority == null)
			throw new IllegalArgumentException("priority is null");
		if (release == null)
			throw new IllegalArgumentException("release is null");
		this.priority = priority;
		this.release = release;

		if (storage == null)
			throw new IllegalArgumentException("storage is null");

		this.storage = storage;
		this.mission = Mission.getMission();

		int backingStoreOfThisMemory;

		if (mission == null && this instanceof MissionSequencer) {
			backingStoreOfThisMemory = MemoryArea.getRemainingMemorySize();
		} else {
			backingStoreOfThisMemory = (int) this.storage.totalBackingStore;
		}

		MemoryArea backingStoreProvider = (mission == null) ? 
				MemoryArea.overAllBackingStore : mission.currMissSeq.missionMemory;

		String privateMemoryName = Memory.getNextMemoryName("PvtMem");		
		
		privateMemory = new PrivateMemory((int) this.storage.getMaxMemoryArea(),
		           backingStoreOfThisMemory,
	               backingStoreProvider, 
	               privateMemoryName);	
		
		this.isRegistered = false;
		this.isInMissionScope = false;
	}

	/*@ 
	  also public behavior
	    requires true;
	 
//	    ensures javax.realtime.Clock.getRealtimeClock().getTime().compareTo(
//	              getLastReleaseTime().add(release.getDeadline())) <= 0;
	  @*/
	public abstract void handleAsyncEvent();

	//	//@ also
	//  //@   requires true;
	//  //@   ensures ??;	// something to add?
	@SCJAllowed(Level.SUPPORT)
	@SCJRestricted(Phase.CLEANUP)
	public void cleanUp() {
		privateMemory.removeArea();
	}

	/**
	 * Registers this event handler with the current mission.
	 */
	//	//@ also
	//  //@   requires true;
	//  //@   ensures ??;	// something to add?
	@SCJAllowed(Level.INFRASTRUCTURE)
	@SCJRestricted(Phase.INITIALIZE)
	public void register() {
		ManagedSchedulableSet hs = mission.msSetForMission;
		hs.addMS(this);
		
		isRegistered = true;
		isInMissionScope = true;
	}

	@SCJAllowed(Level.SUPPORT)
	public void signalTermination() {
	}

	@SCJAllowed(Level.LEVEL_1)
	public AbsoluteTime getLastReleaseTime() {
		// ToDo: implementation
		return null;
	}

	Mission getMission() {
		return mission;
	}

	// Used in JML annotations
	/*@ spec_public @*/PriorityParameters getPriorityParam() {
		return priority;
	}

	// Used in JML annotations
	/*@ spec_public @*/ReleaseParameters getReleaseParam() {
		return release;
	}
}
