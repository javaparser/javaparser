package vm;

public interface ProcessLogic extends Runnable {

	void catchError(Throwable t);
}
