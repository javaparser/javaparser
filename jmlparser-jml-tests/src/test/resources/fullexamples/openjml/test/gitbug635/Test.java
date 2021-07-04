public class Test {

    public static class MyException extends Exception { }

    //@ private exceptional_behavior
    //@   signals_only MyException;
    //@ pure
    private void ThrowPure() throws MyException {
        throw new MyException();
    }

    //@ public normal_behavior
    //@   ensures false;
    public void callerBad() {
        try {
            ThrowPure();
        } catch (MyException e) {
        }
    }
    
    //@ private exceptional_behavior
    //@   signals_only MyException;
    //@ //pure
    private void Throw() throws MyException {
        throw new MyException();
    }

    //@ public normal_behavior
    //@   ensures false;
    public void callerOK() {
        try {
            Throw();
        } catch (MyException e) {
        }
    }
}