package javax.scj.util;

public interface SCJErrorReporter {

	void processExecutionError(Throwable e);

	void processOutOfMemoryError(OutOfMemoryError o);

	void schedulerError(Throwable t);

	String processOutOfBackingStoreError(int start, int end, int left);

}
