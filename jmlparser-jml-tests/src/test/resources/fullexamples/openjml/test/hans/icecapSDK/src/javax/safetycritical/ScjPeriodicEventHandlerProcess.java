package javax.safetycritical;

import vm.Memory;


class ScjPeriodicEventHandlerProcess extends ScjProcess {

	ScjPeriodicEventHandlerProcess(ManagedSchedulable handler, int[] stack) {
		super(handler, stack);
	}
	
	protected void gotoNextState(PriorityFrame pFrame)
	{
		if (state == ScjProcess.State.HANDLED) {
			// finished executing handleAsyncEvent
			if (Mission.getMission().terminationPending()) {
				Mission.getMission().msSetForMission
						.removeMSObject(msObject);
				state = ScjProcess.State.TERMINATED;
			} 
			else {
				state = ScjProcess.State.SLEEPING;
				start();
				pFrame.sleepingQueue.insert(this);
			}
			return;
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
	
	void switchToPrivateMemArea() {
		Memory.switchToArea(((ManagedEventHandler)msObject).privateMemory.getDelegate());
	}
}
