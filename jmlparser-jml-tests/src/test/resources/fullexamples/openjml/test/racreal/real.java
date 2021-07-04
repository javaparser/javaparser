import java.util.LinkedList;
import java.util.List;
import java.math.BigInteger;

public class real {

    // FIXME - what about ++, --, conversion to \real, op=

    public static void main(String... args) {
        //@ ghost \real b = 20;
        //@ ghost \real bb = -b;
        //@ ghost \real zero = 0;
        //@ ghost \real prod = -400;
        //@ assert b + bb == zero;
        //@ assert b * bb == prod;
        //@ assert b + 0 == b;
        //@ assert b > 0;
        //@ assert zero == 0L;
        //@ set zero = 0L;
        //@ assert zero >= 0;
        //@ assert 0.0 + b == b;
        //@ assert b * (double)0 == zero;
        //@ ghost float i = (float)b;
        //@ ghost double l = (double)b;
        //@ assert b == zero;
        //@ ghost Real bi = bb;
        //@ ghost \real bbb = bi;
        //@ assert bbb == bb;
        //@ set bbb = prod + bi;
        //@ assert (\lbl BBB bbb) == -420;
        //@ ghost \real x = new Real(10.30);
        //@ ghost \real xx = (\lbl XX x*10);
        try {
            //@ set bb = bb / zero;
        } catch (Exception e) {
            e.printStackTrace(System.out);
        }
        try {
            //@ set prod /= 0;
        } catch (Exception e) {
            e.printStackTrace(System.out);
        }
        //@ set i += 1;
        //@ set ++i;
        //@ set bbb += 1;
        //@ set ++bbb;
        //@ set bbb++;
        //@ assert (\lbl BBB bbb) == -417;
    }
}
