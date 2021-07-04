package javax.safetycritical;

import vm.Memory;

class ScjMissionSequencerProcess extends ScjProcess {

	ScjMissionSequencerProcess(ManagedSchedulable handler, int[] stack) {
		super(handler, stack);
	}
	
	protected void gotoNextState(PriorityFrame pFrame)
	{
		if (state == ScjProcess.State.HANDLED) {
			// missionSequencer terminates
			if (index == -2) {  // outer sequencer
				msObject.cleanUp();
			} else {
				//devices.Console.println("---- ScjMissionSequencerProcess: " + index + ";target: " + target);
				Mission m = Mission.getMission();
				if (m != null) {
					msObject.cleanUp();
					Mission.getMission().msSetForMission.removeMSObject(msObject);
				}
			}
			state = ScjProcess.State.TERMINATED;
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
