package javax.safetycritical;

import vm.Memory;

class ScjOneShotEventHandlerProcess extends ScjProcess {

	ScjOneShotEventHandlerProcess(ManagedSchedulable handler, int[] stack) {
		super(handler, stack);
	}
	
	protected void gotoNextState(PriorityFrame pFrame)
	{
		if (state == ScjProcess.State.HANDLED) {
			// oneShotHandler finished
			Mission.getMission().msSetForMission.removeMSObject(msObject);
			state = ScjProcess.State.TERMINATED;
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
