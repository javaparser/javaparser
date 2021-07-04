/**************************************************************************
 * File name  : Monitor.java
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

import javax.safetycritical.ScjProcess.State;

import vm.InterruptHandler;
import icecaptools.IcecapCompileMe;

final class Monitor extends vm.Monitor {
	int ceiling;
	private int synchCounter;
	private int priority;
	private ManagedSchedulable owner;
	private InterruptHandler clock;

	Monitor(int ceiling) {
		this.ceiling = ceiling;
		clock = vm.ClockInterruptHandler.instance;
	}
	
	public void lock() {
		clock.disable();
		ManagedSchedulable msObj = PriorityScheduler.instance().getCurrentProcess().getTarget();
		//devices.Console.println(PriorityScheduler.instance().getCurrentProcess().index + " locks ");
		if (owner == null) {
			setOwner(msObj);
		}
			
		if (owner == msObj) {
			synchCounter++;	
			if (synchCounter == 1) {				
				priority = ManagedSchedMethods.getPriorityParameter(msObj).getPriority();
				ManagedSchedMethods.getPriorityParameter(msObj).setPriority(max(priority, ceiling) + 1);
			}
			clock.enable();
		} 
		else {
			// insert the process to in lock queue
			// process in REQUIRELOCK state
			ScjProcess process = ManagedSchedMethods.getScjProcess(msObj);
			process.state = ScjProcess.State.REQUIRELOCK; 
			PriorityScheduler.instance().
				addProcessToLockQueue(this, process);
			//devices.Console.println("addProcessToLockQueue: "  + ManagedSchedMethods.getScjProcess(msObj).index);
			
			// transfer to the process
			clock.enable();
			vm.ClockInterruptHandler.instance.yield();
		}		
	}

	@IcecapCompileMe
	@Override
	public void unlock() {
		clock.disable();
		ManagedSchedulable msObj = PriorityScheduler.instance().getCurrentProcess().getTarget();
		
		//devices.Console.println(PriorityScheduler.instance().getCurrentProcess().index + " unlocks");
		if (owner == msObj) {
			synchCounter--;
			
			if (synchCounter == 0) {
				ManagedSchedMethods.getPriorityParameter(msObj).setPriority(priority);
				// get the next process that needs the lock in lock queue 
				// and assign the lock to this process.
				ScjProcess process = PriorityScheduler.instance().getProcessFromLockQueue(this);
				//if (process != null) devices.Console.println("getProcessFromLockQueue: " + process.index);
				
				if (process != null) {					
					setOwner(process.getTarget());
					
					synchCounter++;
					priority = ManagedSchedMethods.getPriorityParameter(msObj).getPriority();
					ManagedSchedMethods.getPriorityParameter(msObj).setPriority(max(priority, ceiling) + 1);
					// process READY
					process.state = State.READY;
					PriorityScheduler.instance().insertReadyQueue(process);
					//devices.Console.println("insertReadyQueue: " + process.index);
				} 
				else {
					setOwner(null);
				}
			}			
		} 
		else {
			devices.Console.println("    Monitor.unlock: UPS, - not owner");
			clock.enable();
			throw new IllegalMonitorStateException("Not owner on exit");
		}
		clock.enable();
	}
	
	private void setOwner(ManagedSchedulable msObj) {
		owner = msObj;
	}

	private static int max(int x, int y) {
		if (x > y)
			return x;
		else
			return y;
	}
	
	static Monitor getMonitor(Object target) {
		Object obj = getAttachedMonitor(target);
		if (obj == null || !(obj instanceof Monitor)) {
			throw new IllegalMonitorStateException("the target is not a lock:" + obj.toString());
		}
		return (Monitor) obj;
	}
}
