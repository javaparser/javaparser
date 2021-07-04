package thread;

import icecaptools.IcecapCompileMe;

public class ThreadUtils {
	
	@IcecapCompileMe
	private static void dispatchRunnable(Runnable target)
	{
		target.run();
	}
}
