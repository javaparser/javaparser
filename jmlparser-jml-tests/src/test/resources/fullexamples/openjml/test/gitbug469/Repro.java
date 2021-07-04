import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

public class Repro {

public static class Bar {
    private static final FileInputStream URANDOM;

    static {
        FileInputStream tmp = null;
        try {
            tmp = new FileInputStream("/dev/urandom");
        } catch (FileNotFoundException e) {
            tmp = null;
        }
        URANDOM = tmp;
    }


    //@ requires length > 0;
    //@ requires URANDOM.isOpen;
    //@ requires URANDOM.availableBytes > 0;
    private static synchronized void getSeed(int length) {
        int read = 0;
        byte[] result = new byte[length];
        try {
    URANDOM.read(result, read, length-read);
        } catch (final IOException ex) {
            throw new RuntimeException(ex);
        }
    }
    
    private static synchronized void getSeed2(int length) {
        int read = 0;
        byte[] result = new byte[length];
        try {
    URANDOM.read(result, read, length-read);
        } catch (final IOException ex) {
            throw new RuntimeException(ex);
        }
    }
}

}