public class TestException extends RuntimeException {
    //@ requires cause.getMessage()!=null;
    public TestException(final Throwable cause) {
        super(cause.getMessage(), cause);
    }
}