/**************************************************************************
 * File name  : PrioritySchedulerImpl.java
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

import vm.Process;

final class PrioritySchedulerImpl implements vm.Scheduler {
	
	PrioritySchedulerImpl() {		
	}
	
	public Process getNextProcess() {
		vm.ClockInterruptHandler.instance.disable();
		ScjProcess scjProcess = PriorityScheduler.instance().move();
		
		if (scjProcess != null) {
			scjProcess.switchToPrivateMemArea();
			
			vm.ClockInterruptHandler.instance.enable();
			return scjProcess.process;
		}
		PriorityScheduler.instance().stop(
				PriorityScheduler.instance().current.process);
		vm.ClockInterruptHandler.instance.enable();
		return null;
	}

	public void wait(Object target) {
		vm.ClockInterruptHandler.instance.disable();
		
		Monitor monitor = Monitor.getMonitor(target);		
		monitor.unlock();
		
		// process WAITING
		PriorityScheduler.instance().current.state = ScjProcess.State.WAITING;
		PriorityScheduler.instance().pFrame.waitQueue.addProcess(monitor, PriorityScheduler.instance().current);
		//devices.Console.println(">>> To waitQueue: " + PriorityScheduler.instance().current.index);
		
		// move to next process in readyQueue
		PriorityScheduler.instance().moveToNext();
		
		vm.ClockInterruptHandler.instance.enable();
		vm.ClockInterruptHandler.instance.yield();
	}
		
	public void notify(Object target) {
		vm.ClockInterruptHandler.instance.disable();
		
		Monitor monitor = Monitor.getMonitor(target);
		
		ScjProcess process = PriorityScheduler.instance().pFrame.waitQueue.getNextProcess(monitor);
		
		if (process != null) {
			// process in REQUIRELOCK state
			process.state = ScjProcess.State.REQUIRELOCK;
			//devices.Console.println("ScjProcess.State.REQUIRELOCK");
			PriorityScheduler.instance().pFrame.lockQueue.addProcess(monitor, process);
			//devices.Console.println(">>> To lockQueue: " + process.index);
		}
		vm.ClockInterruptHandler.instance.enable();
	}

	public void notifyAll(Object target) {
		vm.ClockInterruptHandler.instance.disable();
		
		Monitor monitor = Monitor.getMonitor(target);

		ScjProcess process = PriorityScheduler.instance().pFrame.waitQueue.getNextProcess(monitor);
		
		while (process != null) {
			
//			if (process != null) {
//				// this if is on grounds of waitForObject(...):
//				if (process.next_temp != null) {
//					PriorityScheduler.instance().pFrame.readyQueue.remove(process);
//					process.next.set(process.next_temp);
//					process.next_temp = null;
//					process.isNotified = true;
//				}
//			}
			// process in REQUIRELOCK state
			process.state = ScjProcess.State.REQUIRELOCK;
			PriorityScheduler.instance().pFrame.lockQueue.addProcess(monitor, process);
//			devices.Console.println(">>> To lockQueue: " + process.index);
			
			process = PriorityScheduler.instance().pFrame.waitQueue.getNextProcess(monitor);
		}
		vm.ClockInterruptHandler.instance.enable();
	}
	
	public Monitor getDefaultMonitor() {
		return null;
	}
	
//	public static boolean waitForObject(Object target, HighResolutionTime time) {
//		vm.ClockInterruptHandler.instance.disable();
//
//		if (time instanceof RelativeTime && 
//			(time.getMilliseconds() < 0L || 
//			 time.getMilliseconds() == 0L && time.getNanoseconds() < 0))
//			throw new IllegalArgumentException("relative time is not vaild");
//
//		if ((time instanceof RelativeTime && 
//			 time.getMilliseconds() == 0 && time.getNanoseconds() == 0) ||
//			 time == null) {
//			vm.Monitor.wait(target);
//			return false;
//		} else {
//			// release the lock.
//			Monitor monitor = Monitor.getMonitor(target);
//			monitor.unlockWithOutEnable();
//			
//			// get current process and reset the boolean value
//			ScjProcess current = PriorityScheduler.instance().current;
//			current.isNotified = false;
//			// save the next release time
//			current.next_temp = new AbsoluteTime(current.next);
//
//			// get current time.
//			AbsoluteTime abs = Clock.getRealtimeClock().getTime(current.next);
//
//			// set the next release time for current process
//			if (time instanceof RelativeTime) {
//				current.next = abs.add((RelativeTime) time, abs);
//			} else if (time instanceof AbsoluteTime) {
//				current.next = new AbsoluteTime((AbsoluteTime) time);
//			} else {
//				throw new UnsupportedOperationException();
//			}
//
//			// get the next process and set appropriate state.
//			ScjProcess nextProcess = PriorityScheduler.instance().pFrame.readyQueue.extractMax();
//			nextProcess.state = ScjProcess.State.EXECUTING;
//			PriorityScheduler.instance().current = nextProcess;
//
//			// insert the current process into the the release queue 
//			// and wait queue.
//			PriorityScheduler.instance().pFrame.sleepingQueue.insert(current);  // ??
//			PriorityScheduler.instance().pFrame.waitQueue.addProcess(monitor, current);
//			
//			// transfer to the current process
//			vm.ClockInterruptHandler.instance.enable();
//			vm.ClockInterruptHandler.instance.yield();
//
//			// if it is notified by time, then the process should get the lock
//			// again to execute and delete the copy in the waitSet.
//			vm.ClockInterruptHandler.instance.disable();
//			if (!PriorityScheduler.instance().current.isNotified) {
//				PriorityScheduler.instance().current.next_temp = null;
//				PriorityScheduler.instance().pFrame.waitQueue.removeProcess(PriorityScheduler.instance().current);
//				monitor.lockWithOutEnable();
//			}
//			vm.ClockInterruptHandler.instance.enable();
//
//			return PriorityScheduler.instance().current.isNotified;
//		}
//	}
}
