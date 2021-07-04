package vm;

import icecaptools.IcecapCompileMe;

import javax.realtime.AbsoluteTime;

import devices.CR16C.KT4585.CR16CRealtimeClock;

public abstract class RealtimeClock {
	private static RealtimeClock instance;

	protected RealtimeClock() {
	}

	@IcecapCompileMe
	public static RealtimeClock getRealtimeClock() {
		if (instance != null) {
			return instance;
		} else {
			switch (Machine.architecture) {
			case Machine.CR16_C:
				instance = new CR16CRealtimeClock();
				break;
			default:
				instance = new DefaultRealtimeClock();
			}
			return getRealtimeClock();
		}
	}

	abstract public int getGranularity();

	abstract public void getCurrentTime(AbsoluteTime now);

	private static class DefaultRealtimeClock extends RealtimeClock {
		@Override
		public int getGranularity() {
			return getNativeResolution();
		}

		@Override
		public void getCurrentTime(AbsoluteTime now) {
			getNativeTime(now); 
			/* 'now' may not be normalized */ 
		}
	}

	/* ==== Clock and Time ================================================ */

	/**
	 * Gets the current resolution of the realtime clock. The resolution is the
	 * nominal interval between ticks. 
	 * 
	 * @return The current resolution of the realtime clock in nanoseconds.
	 */
	private static native int getNativeResolution();

	/**
	 * Gets the current time of the realtime clock Returns Absolute time in
	 * <code>dest</code>.
	 * 
	 * @return 0 if ok, not zero if an error occor.
	 */
	private static native int getNativeTime(AbsoluteTime dest);

	/**
	 * Delay until <code>time</code>.
	 * 
	 * @param time
	 *            is the absolut time
	 */
	public static native void delayNativeUntil(AbsoluteTime time);

	/**
	 * Delay until next system tick 
	 * 
	 */
	public static native void awaitNextTick();
}
