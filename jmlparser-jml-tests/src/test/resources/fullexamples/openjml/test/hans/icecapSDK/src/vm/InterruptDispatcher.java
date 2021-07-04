package vm;

import icecaptools.IcecapCompileMe;

public class InterruptDispatcher {
	protected static InterruptHandler[] handlers;
	protected static int numberOfInterrupts;
	protected static boolean init;

	static final byte HVM_CLOCK = 0;

	protected InterruptDispatcher() {
	}

	private static class NullHandler implements InterruptHandler {

		@Override
		@IcecapCompileMe
		public void handle() {
		}

		@Override
		public void register() {
		}

		@Override
		public void enable() {
		}

		@Override
		public void disable() {
		}
	}

	static {
		init = false;
	}

	@IcecapCompileMe
	public static void registerHandler(InterruptHandler iHandler, byte n) {
		if (n <= numberOfInterrupts) {
			/*
			 * This is a hack to force inclusion of the handler method into the
			 * build
			 */
			/* handlers[n] will never actually be null at this point */
			if (handlers[n] == null) {
				interrupt(n);
			}
			handlers[n] = iHandler;
		}
	}

	@IcecapCompileMe
	private static void interrupt(byte n) {
		handlers[n].handle();
	}

	public static void init() {
		NullHandler nh = new NullHandler();
		for (byte i = 0; i < numberOfInterrupts; i++) {
			handlers[i] = nh;
		}
	}
}
