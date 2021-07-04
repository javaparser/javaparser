import java.util.LinkedList;
import java.util.List;
import java.math.BigInteger;

public class bigint {

    // FIXME - what about ++, --, conversion to \real, op=

    public static void main(String... args) {
        //@ ghost \bigint b = 20;
        //@ ghost \bigint bb = -b;
        //@ ghost \bigint zero = 0;
        //@ ghost \bigint prod = -400;
        //@ assert b + bb == zero;
        //@ assert b * bb == prod;
        //@ assert b + 0 == b;
        //@ assert b > 0;
        //@ assert zero == 0L;
        //@ set zero = 0L;
        //@ assert zero >= 0;
        //@ assert 0L + b == b;
        //@ assert b * (short)0 == zero;
        //@ ghost int i = (int)b;
        //@ ghost long l = (long)b;
        //@ assert b == zero;
        //@ ghost BigInteger bi = bb;
        //@ ghost \bigint bbb = bi;
        //@ assert bbb == bb;
        //@ set bbb = prod + bi;
        //@ assert (\lbl BBB bbb) == -420;
        BigInteger bx = new BigInteger("123456789012345678901234567890");
        //@ ghost \bigint x = new BigInteger("123456789012345678901234567890");
        //@ ghost \bigint xx = (\lbl XX x*10);
        try {
            //@ set bb = bb / zero;
        } catch (Exception e) {
            e.printStackTrace(System.out);
        }
        try {
            //@ set prod = prod / 0;
        } catch (Exception e) {
            e.printStackTrace(System.out);
        }
        //@ set i += 1;
        //@ set ++i;
        //@ set bbb += 1;
        //@ set ++bbb;
        //@ set bbb++;
        //@ assert (\lbl BBB bbb) == -417;
        BigInteger bxx = new BigInteger("123456789012345678901234567890");
        System.out.println((bx!=bxx));
        //@ assert (\lbl TRUE bx != bxx);   // This is an object comparison
        //@ ghost \bigint bix = bx;
        //@ assert (\lbl TRUE bix == bxx);
        //@ assert (\lbl TRUE ((\bigint)bx) == bxx);
        //@ assert (\lbl TRUE bx == (\bigint)bxx);
        
    }
}
