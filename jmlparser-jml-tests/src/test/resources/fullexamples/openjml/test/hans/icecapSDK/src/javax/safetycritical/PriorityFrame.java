/**************************************************************************
 * File name  : PriorityFrame.java
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

import javax.realtime.PeriodicParameters;
import javax.realtime.RelativeTime;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * This frame class holds a ready queue and a sleeping queue 
 * for the priority scheduler. <br>
 * The class is package protected because it is not part of the SCJ 
 * specification.
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
class PriorityFrame {
	PriorityQueue readyQueue;

	SleepingQueue sleepingQueue;  // a priority queue ordered by
								  // ScjProcess.nextActivationTime;

	PriorityQueueForLockAndWait waitQueue;
	PriorityQueueForLockAndWait lockQueue;
	
	PriorityFrame(int queueSize) {
		// create the queues ...
		readyQueue = new PriorityQueue(queueSize);
		sleepingQueue = new SleepingQueue(queueSize);
		
		waitQueue = new PriorityQueueForLockAndWait(queueSize);
		lockQueue = new PriorityQueueForLockAndWait(queueSize);		
	}

	void addProcess(ScjProcess process) {
		if (process.getTarget() instanceof PeriodicEventHandler) {
			//devices.Console.println("PrFrame.addProcess, periodic " + process + ", index " + process.index);

			PeriodicEventHandler pevh = (PeriodicEventHandler) process.getTarget();
			RelativeTime start = ((PeriodicParameters) pevh.release).getStart();

			if (start.getMilliseconds() == 0 && start.getNanoseconds() == 0) {				
				process.state = ScjProcess.State.READY;
				readyQueue.insert(process);
			} else {				
				process.state = ScjProcess.State.SLEEPING;
				sleepingQueue.insert(process);
			}
		}

		else if (process.getTarget() instanceof MissionSequencer) {
			//devices.Console.println("PrFrame.addProcess, missSeq " + process+ ", index " + process.index);
			process.state = ScjProcess.State.READY;
			readyQueue.insert(process);
		}

		else if (process.getTarget() instanceof AperiodicEventHandler) {
			//devices.Console.println("PrFrame.addProcess, aperiodic " + process+ ", index " + process.index);
			process.state = ScjProcess.State.BLOCKED;
		}

		else if (process.getTarget() instanceof OneShotEventHandler) 
		{
			//devices.Console.println("PrFrame.addProcess, oneshot " + process+ ", index " + process.index);
			process.state = ScjProcess.State.SLEEPING;
			sleepingQueue.insert(process);			
		}
		
		// if a thread is added, then it is made blocked and waiting 
		// for the call to start.
		else if (process.getTarget() instanceof ManagedThread) {
			//devices.Console.println("PrFrame.addProcess, managedThread " + process+ ", index " + process.index);
			//if (((ManagedThread) process.getTarget()).isAutoStart()) {
				process.state = ScjProcess.State.READY;
				readyQueue.insert(process);
			//} else {
			//	process.state = ScjProcess.State.BLOCKED;
			//}
		}

		else {
			throw new IllegalArgumentException("PriorityFrame.addProcess: another schedulable object ?");
		}
	}

	public void removeFromQueue(ScjProcess scjProcess) {
		readyQueue.remove(scjProcess);
		sleepingQueue.remove(scjProcess);
		waitQueue.removeProcess(scjProcess);
		lockQueue.removeProcess(scjProcess);		
	}
}
