package javax.safetycritical;

import vm.Memory;


class ScjManagedThreadProcess extends ScjProcess {

	ScjManagedThreadProcess(ManagedSchedulable handler, int[] stack) {
		super(handler, stack);
	}

	protected void gotoNextState(PriorityFrame pFrame)
	{
		if (state == ScjProcess.State.HANDLED) {
			// thread finished and removed.
			Mission.getMission().msSetForMission.removeMSObject(msObject);
			//devices.Console.println("ScjManagedThreadProcess: terminate: " + this);
			state = ScjProcess.State.TERMINATED;
		} 
		else if (state == ScjProcess.State.SLEEPING) {
			pFrame.sleepingQueue.insert(this);
		}		
		else if (state == ScjProcess.State.WAITING) {
			;
		}
		else if (state == ScjProcess.State.REQUIRELOCK) {
			;
		}
		else {
			state = ScjProcess.State.READY;
			pFrame.readyQueue.insert(this);
		}
	}

	@Override
	void switchToPrivateMemArea() {
		Memory.switchToArea(((ManagedThread)msObject).privateMemory.getDelegate());
	}
}
