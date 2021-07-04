package javax.scj.util;

public class SilentSCJErrorReporter implements SCJErrorReporter {
	@Override
	public void processExecutionError(Throwable e) {
	}

	@Override
	public void processOutOfMemoryError(OutOfMemoryError o) {
	}

	@Override
	public void schedulerError(Throwable t) {
	}

	@Override
	public String processOutOfBackingStoreError(int start, int end, int left) {
		return "";
	}
}
