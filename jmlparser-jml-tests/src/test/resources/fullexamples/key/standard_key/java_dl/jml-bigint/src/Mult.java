/** This is an example to illustrate JML's \bigint type,
 * which always represents mathematical integers no matter what
 * Java integer semantics are in force.
 */
public class Mult {

    // Without any pre condition, this post condition is not valid
    // in the checking-overflow semantics.
    // To prove it, we need to assume that the (mathematical) product
    // is within the bounds of Java integers,
    // which means we have to express this property using a different
    // (ignoring-overflow) semantics.

    /*@ public normal_behavior
      @ requires -2147483648 < x;
      @ requires -2147483648 < (\bigint)x * (\bigint)y;
      @ requires (\bigint)x * (\bigint)y <= 2147483647;
      @ ensures \result == x * y;
      @*/
    public int mult (int x, int y){
        int z = 0;
        boolean n = x < 0;
        if (n) x = -x;
	//@ ghost int oldx = x;
	//@ ghost \bigint p = 0;
	/*@ maintaining 0 <= x && x <= oldx;
          @ maintaining z == y * (oldx - x);
	  @ maintaining (\bigint)z == p;
          @ decreasing  x;
	  @*/
        while (x-- > 0) {
	    //@ set p = p + (\bigint)y;
	    z += y;
        }
        return n? -z: z;
    }

// this example involving a narrowing cast 
// only works with Java integer semantics in force

    //@ ghost byte b;

    //@ ensures b == 0;
    public void cast () {
        //@ ghost \bigint z = 256;
        //@ set b = (byte) z;
        {}
    }
}
