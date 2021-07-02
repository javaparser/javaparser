class Loop1 {
    /*@ public invariant x>=0; @*/
    private /*@ spec_public @*/ int x;

    /*@ public normal_behavior
      @ requires x>=0;
      @ assignable \nothing;  // this is a ** constructor **, so the object does not yet exist, 
      @                       // hence "this" object's fields do not need to be in the assignable
      @ ensures this.x == x;
      @*/
    public Loop1(int x) {
        this.x = x;
    }

    /*@ public normal_behavior 
      @ assignable \nothing;
      @ ensures \result == x * x;
      @*/
    public int method1() {
        int y = x;
        int z = 0;
        /*@ loop_invariant
          @  (y >= 0) && (x * y + z == x * x) ;
          @ assignable \nothing; // only heap locations need to be explicitly mentioned 
          @ // (possibly modified local variables are anonymized automatically by the loop invariant rule)
          @ // you can list them in the assignable clause but it is not necessary and they are actually ignored
          @ decreasing y ;
          @*/
        while (y > 0) {
            z = z + x;
            y = y - 1;
        }
        return z;
    }
}
