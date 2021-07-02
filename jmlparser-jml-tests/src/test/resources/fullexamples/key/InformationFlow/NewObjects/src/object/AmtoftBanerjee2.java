package object;


/**
 *
 * @author christoph
 */
public class AmtoftBanerjee2 {
    int marg, res;
    //@ invariant (marg != 0) ==> (res == expensive(marg));

    //@ normal_behavior
    //@ assignable marg, res;
    //@ determines z, \result \by \itself;
    int cexp(int z) {
        if (z == marg && z != 0) {
            return res;
        } else {
            int result = expensive(z);
            marg = z;
            res = result;
            return result;
        }
    }

    // The accessible clause can be proved automatically, if the query treatment
    // is set to "off" and expand local queries is set to "on".
    // Note: This method is final to allow for modularly sound method expansion
    //@ normal_behavior
    //@ ensures \result == expensive(z);
    //@ assignable \strictly_nothing;
    //@ accessible \nothing;
    //@ determines z, \result \by \itself;
    //@ helper
    final int expensive(int z) {
        return z;
    }
}
