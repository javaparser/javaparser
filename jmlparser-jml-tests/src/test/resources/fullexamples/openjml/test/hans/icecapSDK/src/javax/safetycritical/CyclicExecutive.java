/**************************************************************************
 * File name  : CyclicExecutive.java
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
import javax.realtime.Clock;
import javax.realtime.RelativeTime;
import javax.safetycritical.annotate.Level;
import javax.safetycritical.annotate.Phase;
import javax.safetycritical.annotate.SCJAllowed;

/**
 * A <code>CyclicExecutive</code> represents a Level 0 mission. Every mission 
 * in a Level 0 application must be a subclass of <code>CyclicExecutive</code>.
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, 
 * <A HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 * Hans S&oslash;ndergaard, VIA University College, Denmark, 
 * <A HREF="mailto:hso@viauc.dk">hso@via.dk</A> 
 */
@SCJAllowed
public abstract class CyclicExecutive extends Mission {
	Clock rtClock;
	AbsoluteTime next;
	RelativeTime deltaTime;

	@SCJAllowed
	public CyclicExecutive() {
		this.rtClock = Clock.getRealtimeClock();
		this.next = rtClock.getTime();
		this.deltaTime = new RelativeTime(rtClock);
	}

	/**
	 * Every <code>CyclicExecutive</code> shall provide its own cyclic schedule, which is represented
	 * by an instance of the <code>CyclicSchedule</code> class. Application programmers are expected to override
	 * the <code>getSchedule</code> method to provide a schedule that is appropriate for the mission.<br>
	 * Level 0 infrastructure code invokes the <code>getSchedule</code> method on the mission returned from 
	 * <code>MissionSequencer.getNextMission</code> after invoking the mission's <code>initialize</code> method 
	 * in order to obtain the desired cyclic schedule. <br>
	 * Upon entry into the <code>getSchedule</code> method, this mission's <code>MissionMemory</code> area shall be the
	 * active allocation context. The value returned from <code>getSchedule</code> must reside in the current 
	 * mission's <code>MissionMemory</code> area or in some enclosing scope. <br>
	 * Infrastructure code shall check that all of the <code>PeriodicEventHandler</code> objects referenced
	 * from within the returned <code>CyclicSchedule</code> object have been registered for execution with this mission.  
	 * 
	 * @param handlers The handlers that have been registered with <code>this Mission</code>. 
	 * The handler objects must reside in an enclosing scope of <code>this</code>.
	 * @return A cyclic schedule for the handlers.
	 */
	@SCJAllowed(Level.INFRASTRUCTURE)
	public abstract CyclicSchedule getSchedule(PeriodicEventHandler[] handlers);

	
	void runInitialize() {
	    // overrides the method in class Mission and is called in mission memory
		phaseOfMission = Phase.INITIALIZE;
		msSetForMission = new ManagedSchedulableSet();
		initialize();
	}
	
	/**
	 * Implementation of a cyclic executive.
	 * Is invoked in a mission memory scope.
	 */
	void runExecute()
	// overrides the method in class Mission and is called in mission memory
	{
		// The following four lines of code: to meet the precondition in getSchedule.
		ManagedSchedulable[] msObjects = Mission.getMission().msSetForMission.managedSchObjects;
		PeriodicEventHandler[] pevs = new PeriodicEventHandler[Mission.getMission().msSetForMission.noOfRegistered];
		
		for (int i = 0; i < pevs.length; i++)
			pevs[i] = (PeriodicEventHandler)msObjects[i];
		
		CyclicSchedule schedule = getSchedule(pevs) ;

		/**
		 * local reference to frames
		 */
		final Frame[] frames = schedule.getFrames();
		
		/**
		 * step is the minor cycle counter
		 */
		int step = 0;

		while (!missionTerminate) {
			PeriodicEventHandler[] handlers = frames[step].handlers;
			int n = handlers.length;

			for (int handlerIdx = 0; handlerIdx < n; handlerIdx++) {
				handlers[handlerIdx].privateMemory.enter(handlers[handlerIdx]);
			}

			// wait for frame.duration to expire 
			waitForNextFrame(frames[step].duration);

			// index to next frame
			step = (step + 1) % frames.length;
		}
	}

	void runCleanup(MissionMemory missMem)
	//overrides the method in class Mission and is called in mission memory
	{
		vm.ClockInterruptHandler.instance.disable();
		
		Mission.getMission().msSetForMission.terminateMSObjects();
		
		cleanUp();
		missMem.resetArea();
		vm.ClockInterruptHandler.instance.enable();
	}

	private void waitForNextFrame(RelativeTime duration) {
		next.add(duration, next);
		vm.RealtimeClock.delayNativeUntil(next);
	}

	// Used in feasible below
	/*static private int find(PeriodicEventHandler[] handlerList,
			PeriodicEventHandler h) {
		for (int i = handlerList.length - 1; i >= 0; i--)
			if (handlerList[i] == h)
				return i;
		return -1;
	}*/

	// Used in JML annotations
//	boolean feasible(PeriodicEventHandler[] handlerList, CyclicSchedule schedule) {
//		// checks a cyclic schedule. It is assumed, conservatively, that every handler runs to its deadline.
//
//		RelativeTime[] nextDeadline = new RelativeTime[handlerList.length];
//		for (int h = 0; h < handlerList.length; h++)
//			nextDeadline[h] = new RelativeTime(
//					handlerList[h].release.getDeadline());
//
//		Frame[] frames = schedule.getFrames();
//
//		RelativeTime next = new RelativeTime();
//
//		for (int step = 0; step < frames.length; step++) {
//			PeriodicEventHandler[] handlers = frames[step].handlers;
//			PeriodicEventHandler hx;
//			int n = handlers.length;
//			RelativeTime startFrame = new RelativeTime(next);
//
//			for (int handlerIdx = 0; handlerIdx < n; handlerIdx++) {
//				hx = handlers[handlerIdx];
//				// check handler declared
//				int h = find(handlerList, hx);
//				if (h < 0)
//					return false;
//				// run handler hx
//				next.add(hx.release.getDeadline());
//				// check against absolute deadline
//				if (next.compareTo(nextDeadline[h]) > 0)
//					return false;
//				nextDeadline[h].add(((PeriodicParameters) hx.release)
//						.getPeriod());
//			}
//			// advance to next frame
//			if (next.compareTo(startFrame.add(frames[step].duration)) > 0)
//				return false;
//			next.add(frames[step].duration);
//		}
//		// the schedule was OK for handlers in the frames
//		// check no handler left behind.
//		for (int h = 0; h < handlerList.length; h++)
//			if (nextDeadline[h].compareTo(next) <= 0)
//				return false;
//
//		return true;
//	}
}
