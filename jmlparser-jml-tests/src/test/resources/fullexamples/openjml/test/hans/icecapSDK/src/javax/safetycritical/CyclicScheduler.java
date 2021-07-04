/**************************************************************************
 * File name  : CyclicScheduler.java
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

import javax.realtime.Scheduler;
import javax.safetycritical.MissionSequencer.State;
import javax.scj.util.Const;

import vm.Monitor;
import vm.Process;

/**
 * 
 * @version 1.2; - December 2013
 * 
 * @author Anders P. Ravn, Aalborg University, <A
 *         HREF="mailto:apr@cs.aau.dk">apr@cs.aau.dk</A>, <br>
 *         Hans S&oslash;ndergaard, VIA University College, Denmark, <A
 *         HREF="mailto:hso@viauc.dk">hso@via.dk</A>
 * 
 * @scjComment - implementation issue: infrastructure class; 
 *   not part of the SCJ specification.
 */
final class CyclicScheduler extends Scheduler implements vm.Scheduler {
	MissionSequencer<?> seq;

	private ScjProcess current;

	private static CyclicScheduler scheduler;

	/**
	 * 
	 * @return The cyclic scheduler.
	 */
	static CyclicScheduler instance() {
		if (scheduler == null) {
			scheduler = new CyclicScheduler();
		}
		return scheduler;
	}

	private CyclicScheduler() {
		int[] sequencerStack = new int[Const.HANDLER_STACK_SIZE_DEFAULT];

		vm.ClockInterruptHandler.initialize(this, sequencerStack);
	}

	public Process getNextProcess() {
		ScjProcess scjProcess = CyclicScheduler.instance().getCurrentProcess();

		if (scjProcess.getTarget() instanceof MissionSequencer<?>
				&& ((MissionSequencer<?>) (scjProcess.getTarget())).currState == State.END) {
			scjProcess.getTarget().cleanUp();
			CyclicScheduler.instance().stop(scjProcess.process);
		}

		return scjProcess.process;
	}

	private vm.Process mainProcess;

	private void processStart() {
		vm.ClockInterruptHandler clockHandler = vm.ClockInterruptHandler.instance;
		mainProcess = new vm.Process(null, null);

		clockHandler.register();
		clockHandler.enable();
		clockHandler.startClockHandler(mainProcess);
		clockHandler.yield();
	}

	@IcecapCompileMe
	void stop(vm.Process current) {
		current.transferTo(mainProcess);
	}

	void start(MissionSequencer<?> seq) {
		this.seq = seq;

		current = ManagedSchedMethods.createScjProcess(seq); 
		processStart();
	}

	ScjProcess getCurrentProcess() {
		return current;
	}

	public void wait(Object target) {

	}

	public void notify(Object target) {

	}

	public void notifyAll(Object target) {
	}

	public Monitor getDefaultMonitor() {
		return null;
	}

}
