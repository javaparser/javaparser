public class CompleteResolutionExample {
    int x;
    int y;
    int z;

    /*@ public normal_behavior
        forall String next;
        ensures x == y;
        ensures next != null ;
     */
    public void foo(int y/*!label=paramY*/) {
        /*@ ghost boolean Q = next //!ref: faNext
                                !=null;
         */
    }

    /*@
        invariant (\forall int x//!ref: bindX
                        ; x //!ref: bindX
                        > 0;
                        x //!ref: bindX
                            !=
                                (\num_of int x//!bindX2;
                                        x //!ref:bindX2
                                        > 0; 1));
     */
}