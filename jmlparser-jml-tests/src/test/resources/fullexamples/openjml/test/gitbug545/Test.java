// This example was infeasible as a default method of an interface, but was not as a regular member of a class

public interface Test {
    
    //@ requires length >= 0;
    default public byte[] getArray(int length) {
        byte[] b = new byte[length];
        return b;
    }
}