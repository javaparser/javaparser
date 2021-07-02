package mini;

/**
 *
 * @author christoph
 */
public class DifferenceSeqLocset {
    public boolean b;
    public static D l1, l2, l3;
    
    //@ invariant l3 == l1 || l3 == l2;
    //@ invariant l1 != l2;
    
    /*@ normal_behavior
      @     determines \locset(l1.b, l2.b, l3.b) \by \itself;
      @
      @ normal_behavior
      @     determines l1.b, l2.b, l3.b \by \itself;
      @*/
    void m() {
        if (b) {
            l3 = l1;
        } else {
            l3 = l2;
        }
    }
}

class D {
    public boolean b;
}
