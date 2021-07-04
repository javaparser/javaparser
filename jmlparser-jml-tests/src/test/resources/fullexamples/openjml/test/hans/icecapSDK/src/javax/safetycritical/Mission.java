/**************************************************************************
 * File name  : Mission.java
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

import javax.realtime.AbsoluteTime;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;
import javax.scj.util.Const;

/**
 * An SCJ application is comprised of one or more <code>Mission</code> objects.
 * Each <code>Mission</code> object is implemented as a subclass of this
 * abstract <code>Mission</code> class.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * 
 * @scjComment 
 */
@SCJAllowed
public abstract class Mission {
	MissionSequencer<?> currMissSeq;

	boolean missionTerminate = false;

	ManagedSchedulableSet msSetForMission; 
	Phase phaseOfMission;

	protected int missionIndex = -1;

	static volatile Mission[] missionSet = null;

	boolean isMissionSetInitByThis = false;

	static volatile boolean isMissionSetInit = false;

	@SCJAllowed
	public Mission(AbsoluteTime start) {
		// ToDo: implement
	}
	
	@SCJAllowed
	public Mission() {
	}

	/** 
	 * Method to clean up after a mission terminates. <br> The infrastructure calls 
	 * <code>cleanup</code> after all <code>ManagedSchedulable</code>s 
	 * associated with this <code>Mission</code> have terminated, but before
	 * control leaves the dedicated <code>MissionMemory</code> area. 
	 * The default implementation of <code>cleanup</code> does nothing.
	 */
	@SCJAllowed(Level.SUPPORT)
	protected boolean cleanUp() {
		return true;
	}

	@SCJAllowed
	@IcecapCompileMe
	public static Mission getMission() {
		Mission mission = null;
		
		if (Launcher.level == 0 && CyclicScheduler.instance().seq != null) {
			mission = CyclicScheduler.instance().seq.currMission;
		} 
		else if (Launcher.level > 0 && PriorityScheduler.instance().getCurrentProcess() != null) {
					
			if (PriorityScheduler.instance().getCurrentProcess().getTarget() instanceof MissionSequencer) {
				mission = 
					((MissionSequencer<?>) PriorityScheduler.instance().getCurrentProcess().getTarget()).currMission;
			} 
			else {
				mission = ManagedSchedMethods.getMission(PriorityScheduler.instance().getCurrentProcess().getTarget());
			}
		} 
		return mission;
	}

	@SCJAllowed
	public MissionSequencer<?> getSequencer() {
		return currMissSeq;
	}

	/**
	 * Performs initialization of this <code>Mission</code>. The infrastructure 
	 * calls <code>initialize</code> after the <code>Mission</code> has been 
	 * instantiated and the <code>MissionMemory</code> has been resized to 
	 * match the size returned from this <code>Mission</code>'s <code>
	 * missionMemorySize</code> method. Upon entry into the <code>initialize</code>
	 * method, the current allocation context is the <code>MissionMemory</code> 
	 * area dedicated to this particular <code>Mission</code>. <p>
	 * 
	 * An overridden implementation of <code>initialize</code> should instantiate 
	 * and register all <code>ManagedSchedulable</code>s that constitute this 
	 * <code>Mission</code>. The infrastructure enforces that <code>
	 * ManagedSchedulable</code>s can only be instantiated and registered if 
	 * the infrastructure is currently executing a <code>Mission.initialize</code> method. 
	 * An exception to this rule allows a <code>MissionSequencer</code> to be 
	 * instantiated if the infrastructure is currently executing
	 * <code>Safelet.getSequencer</code>. <p>
	 * The infrastructure arranges to begin executing the <code>ManagedSchedulable</code>s 
	 * registered by the <code>initialize</code> method upon return from 
	 * the <code>initialize</code> method.
	 */
	@SCJAllowed(Level.SUPPORT)
	protected abstract void initialize();

	// used in MissionSequencer.handleAsyncEvent: case State.INITIALIZE
	void setMissionSeq(MissionSequencer<?> missSeq) {
		currMissSeq = missSeq;
	}

	/**
	 * The application developer is required to implement this method.
	 * @return The desired size of this mission's <code>MissionMemory</code>, measured in bytes.
	 */
	@SCJAllowed(Level.SUPPORT)
	public abstract long missionMemorySize();

	/**
	 * This method provides a standard interface for requesting termination of a mission. <p>
	 * The infrastructure shall: 
	 * <ol>
	 * <li> disable all periodic event handlers associated with this <code>Mission</code>,
	 * <li> remove handlers from <code>AperiodicEvent</code>s, 
	 * <li> clear the fire count for each of this <code>Mission</code>'s event handlers 
	 * <li> wait for all dispatched schedulables to terminate execution, 
	 * <li> invoke the <code>cleanup</code> method for each of the 
	 *      <code>ManagedSchedulable</code>s associated with this mission, and 
	 * <li> invoke the <code>cleanup</code> method associated with this mission.
	 * </ol>
	 * <p>
	 * 
	 * An application-specific subclass of <code>Mission</code> may override 
	 * this method in order to insert application-specific code to communicate 
	 * the intent to shutdown to specific <code>ManagedSchedulable</code>s. <p>
	 * Control returns from <code>requestTermination</code> after it has 
	 * arranged for the required activities to be performed. 
	 * Note that those activities may not have completed.
	 */
	@SCJAllowed
	public final boolean requestTermination() {
		if (missionTerminate == false) {	// called the first time during mission execution	
		
		  // terminate all the sequencer's MSObjects that were created by the mission.

		  for (int i = 0; i < msSetForMission.noOfRegistered; i++) {
			if (msSetForMission.managedSchObjects[i] != null) {
				msSetForMission.managedSchObjects[i].signalTermination();
			}
		  }
		  
		  missionTerminate = true;
		  return false;
		}
		else
			return true;  // called more than once: nothing done
	}

	/**
	 * Checks if the current mission is trying to terminate.
	 * 
	 * @return True if and only if this <code>Mission</code> object's <code>
	 *         Mission.requestTermination</code> method has been invoked.
	 */
	public final boolean terminationPending() {
		return missionTerminate;
	}

	static synchronized int addNewMission(Mission mission) {
		for (int i = 0; i < missionSet.length; i++) {
			if (missionSet[i] == null) {
				missionSet[i] = mission;
				return i;
			}
		}
		throw new IndexOutOfBoundsException("Mission set: too small");
	}

	void runInitialize() {
		vm.ClockInterruptHandler.instance.disable();

		if (missionSet == null || isMissionSetInit == false) {
			missionSet = new Mission[Const.DEFAULT_HANDLER_NUMBER];
			isMissionSetInitByThis = true;
			isMissionSetInit = true;
		}
		missionIndex = addNewMission(this);

		phaseOfMission = Phase.INITIALIZE;  // used by JML ??
		msSetForMission = new ManagedSchedulableSet();
		initialize();

		vm.ClockInterruptHandler.instance.enable();
	}

	void runExecute()
	//  Called in mission memory. 
	//  This implementation is for priority schedule execution.
	//  For cyclic schedule execution, this method is overwritten in 
	//  the subclass CyclicExecutive. 
	{
		vm.ClockInterruptHandler.instance.disable();

		phaseOfMission = Phase.EXECUTE;
		ManagedSchedulableSet msSet = msSetForMission;
		PriorityFrame frame = PriorityScheduler.instance().pFrame;
		
		int index = missionIndex * 20;
		
		for (int i = 0; i < msSet.noOfRegistered; i++) {
			
			ManagedSchedulable ms = msSet.managedSchObjects[i];
			
			msSet.scjProcesses[i] = ManagedSchedMethods.createScjProcess(ms);
			msSet.scjProcesses[i].setIndex(index);
			index++;			
			frame.addProcess(msSet.scjProcesses[i]);
		}

		vm.ClockInterruptHandler.instance.enable();
	}

	void runCleanup(MissionMemory missMem)
	//  Called in mission memory. 
	//  This implementation is for priority schedule execution.
	//  For cyclic schedule execution, this method is overwritten in 
	//  the subclass CyclicExecutive. 
	{
		phaseOfMission = Phase.CLEANUP;
		// wait until (all handlers in mission have terminated)			
		while (msSetForMission.msCount > 0) {
			vm.RealtimeClock.awaitNextTick();
		}

		vm.ClockInterruptHandler.instance.disable();
		for (int i = 0; i < msSetForMission.noOfRegistered; i++) {
			msSetForMission.scjProcesses[i] = null;
			msSetForMission.managedSchObjects[i] = null;
		}

		missionSet[missionIndex] = null;
		if (isMissionSetInitByThis == true) {
			isMissionSetInit = false;
		}
		cleanUp();
		missMem.resetArea();
		vm.ClockInterruptHandler.instance.enable();
	}

	protected static ScjProcess getScjProcess(int missionIndex,
			int scjProcessIndex) {
		return missionSet[missionIndex].msSetForMission.scjProcesses[scjProcessIndex];
	}

	// used for JML annotation only (not public)
	boolean isRegistered(ManagedSchedulable target) {
		return ManagedSchedMethods.isRegistered(target);
	}

	// used for JML annotation only (not public)
	boolean inMissionScope(ManagedSchedulable target) {
		return ManagedSchedMethods.isInMissionScope(target);
	}

	// used for JML annotation only (not public)
	boolean inMissionScope(CyclicSchedule cs) {
		return true;
	}

	// used for JML annotation only (not public)
	Phase getPhase() {
		return phaseOfMission;
	}

}
