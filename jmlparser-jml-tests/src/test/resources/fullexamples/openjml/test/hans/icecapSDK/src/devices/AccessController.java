package devices;

import icecaptools.IcecapCompileMe;
import sun.security.action.GetPropertyAction;

import java.security.PrivilegedAction;

public class AccessController {

    @SuppressWarnings("unchecked")
    @IcecapCompileMe
    public static <T> T doPrivileged(PrivilegedAction<T> action) {
        if (action instanceof GetPropertyAction) {
            GetPropertyAction gpa = (GetPropertyAction) action;
            String prop = gpa.run();
            return (T) prop;
        }
        return (T) new Boolean(false);
    }
}
