package javax.safetycritical;

import javax.realtime.PriorityParameters;

final class ManagedSchedMethods {
	
	static PriorityParameters getPriorityParameter(ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).priority;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).priority;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).priority;
		else
			return null;
	}

	static ScjProcess getScjProcess(ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).process;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).process;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).process;
		else
			return null;
	}
	
	static StorageParameters getStorage(ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).storage;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).storage;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).storage;
		else
			return null;
	}
	
	private static ScjProcess createScjProcess(ManagedSchedulable target, int[] ps) {
		if (target instanceof PeriodicEventHandler) {
			return new ScjPeriodicEventHandlerProcess(target, ps);
		} else if (target instanceof OneShotEventHandler) {
			return new ScjOneShotEventHandlerProcess(target, ps);
		} else if (target instanceof MissionSequencer<?>) {
			return new ScjMissionSequencerProcess(target, ps);
		} else if (target instanceof AperiodicEventHandler) {
			return new ScjAperiodicEventHandlerProcess(target, ps);
		} else if (target instanceof ManagedThread) {
			return new ScjManagedThreadProcess(target, ps);
		} else {
			return null;
		}
	}
	
	static ScjProcess createScjProcess(ManagedSchedulable target)
	{
		return createScjProcess(target, new int[(int)getStorage(target).configurationSizes[0]]);
	}
	
	static Mission getMission (ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).mission;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).mission;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).mission;
		else
			return null;
	}
	
	static boolean isRegistered (ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).isRegistered;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).isRegistered;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).isRegistered;
		else
			return false;
	}
	
	static boolean isInMissionScope (ManagedSchedulable target)
	{
		if (target instanceof ManagedEventHandler)
			return ((ManagedEventHandler)target).isInMissionScope;
		else if (target instanceof ManagedThread)
			return ((ManagedThread)target).isInMissionScope;
		else if (target instanceof ManagedLongEventHandler)
			return ((ManagedLongEventHandler)target).isInMissionScope;
		else
			return false;
	}
}
