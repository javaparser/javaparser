
public class TestException extends RuntimeException {
	private static final long serialVersionUID = 0L;

	//@ requires cause != null;
	public TestException(final Throwable cause) {
        super("abc", cause);
        //@ assert this != cause;
    }

}
