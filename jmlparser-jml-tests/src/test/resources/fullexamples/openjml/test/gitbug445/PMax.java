public class PMax implements Proc<Integer,Integer> {
    protected /*@ spec_public @*/ Integer maxSeen = Integer.MIN_VALUE;
                                    //@ in objectState; 
    /*@ also assignable maxSeen;
      @ ensures maxSeen == Math.max(\old(maxSeen),x); @*/
    public Integer run(Integer x) {
        if (x > maxSeen) {
            maxSeen = x;
        }
        return x;
    }
    //@ ensures \result == maxSeen;
    public /*@ pure @*/ Integer getMax() { return maxSeen; }
}
