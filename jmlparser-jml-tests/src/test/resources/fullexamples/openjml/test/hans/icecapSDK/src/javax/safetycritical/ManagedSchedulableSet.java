/**************************************************************************
 * File name  : ManagedSchedulableSet.java
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
 *    
 * Description: 
 * 
 * Revision history:
 *   date   init  comment
 *
 *************************************************************************/

package javax.safetycritical;

import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;
import javax.scj.util.Const;

/**
 * This collection class of handlers is created in mission memory and used 
 * by the mission.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment 
 *  - implementation issue: infrastructure class; not part of the SCJ specification.
 */
@SCJAllowed(Level.INFRASTRUCTURE)
class ManagedSchedulableSet {
	ManagedSchedulable[] managedSchObjects = 
		new ManagedSchedulable[Const.DEFAULT_HANDLER_NUMBER];
	int noOfRegistered = 0;

	ScjProcess[] scjProcesses = new ScjProcess[Const.DEFAULT_HANDLER_NUMBER];

	/**
	 * Count of ManagedSchedulable objects for the mission. 
	 * Only one mission at a time; no sub-mission
	 * 
	 * The msCount is incremented by addMS,
	 * and is decremented by PriorityScheduler when MS object is terminated.
	 * 
	 * Mission.runCleanup is waiting until msCount == 0
	 */
	int msCount;

	ManagedSchedulableSet() {
	}

	/*@ 
	  behavior
	    requires ms != null;
	    ensures this.contains(ms);
	  @*/
	void addMS(ManagedSchedulable ms) {
		if (!contains(ms)) {
			managedSchObjects[noOfRegistered] = ms;
			noOfRegistered++;
			msCount++;
		}
	}

	boolean contains(ManagedSchedulable ms) {
		for (int i = 0; i < noOfRegistered; i++) {
			if (managedSchObjects[i] == ms)
				return true;
		}
		return false;
	}

	void terminateMSObjects() // stop all managed schedule objects; called in CyclicExecutive.runCleanup
	{
		for (int i = noOfRegistered; i > 0; i--) {
			managedSchObjects[i - 1].cleanUp();
			managedSchObjects[i - 1] = null;
			msCount--;
		}
	}

	void removeMSObject(ManagedSchedulable ms) // called in Scj...Process.gotoNextState
	{
		for (int i = 0; i < noOfRegistered; i++) {
			if (managedSchObjects[i] == ms) {
				managedSchObjects[i].cleanUp();
				managedSchObjects[i] = null;
				
				//PriorityScheduler.instance().pFrame.readyQueue.remove(scjProcesses[i]);
				
				PriorityScheduler.instance().pFrame.removeFromQueue (scjProcesses[i]);
				//devices.Console.println("MSSet.removeMSObject " + scjProcesses[i].index);
				
				scjProcesses[i] = null;
				msCount--;
			}
		}
		//devices.Console.println("MSSet.removeMSObject: msCount " + msCount);
		if (msCount == 0)
			ManagedSchedMethods.getMission(ms).getSequencer().seqNotify();
	}

	void removeAperiodicHandlers() // remove all aperiodic handlers; 
	// called in PriorityScheduler.move()
	{
		for (int i = 0; i < noOfRegistered; i++) {
			if (managedSchObjects[i] instanceof AperiodicEventHandler) {
				managedSchObjects[i].cleanUp();
				PriorityScheduler.instance().pFrame.readyQueue
						.remove(scjProcesses[i]);
				msCount--;
			}
			
			if (msCount == 0)
				ManagedSchedMethods.getMission(managedSchObjects[i]).getSequencer().seqNotify();
		}
	}

	int indexOf(ManagedSchedulable ms) {
		for (int i = 0; i < noOfRegistered; i++) {
			if (managedSchObjects[i] == ms)
				return i;
		}
		return -1;
	}

	public String toString() {
		return "Mission: " + noOfRegistered + " handlers";
	}
}