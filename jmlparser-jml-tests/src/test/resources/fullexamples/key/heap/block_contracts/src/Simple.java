public class Simple {

    // Automatically provable with block contracts on and basic arithmetics.
    /*@ public normal_behavior
      @ ensures i <  0 && j <  0 ==> \result == (-i) + (-j);
      @ ensures i <  0 && j >= 0 ==> \result == (-i) +   j;
      @ ensures i >= 0 && j <  0 ==> \result ==   i  + (-j);
      @ ensures i >= 0 && j >= 0 ==> \result ==   i  +   j;
      @ assignable \nothing;
      @*/
    public int addAbsoluteValues(int i, int j) {
        /*@ ensures i >= 0 && (i == \before(i) || i == -\before(i));
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            if (i < 0) i = -i;
        }
        /*@ normal_behavior
          @ ensures j >= 0 && (j == \before(j) || j == -\before(j));
          @ diverges false;
          @ assignable \nothing;
          @*/
        label: {
            if (j >= 0) break label;
            j = -j;
        }
        return i + j;
    }

    // Automatically provable with block contracts on,
    // loop invariants on and basic arithmetics.
    /*@ requires x >= 0;
      @ ensures \result == x * x;
      @ signals_only \nothing;
      @ diverges false;
      @ assignable \nothing;
      @*/
    public int square(int x) {
        int y = 0;
        int i = 0;
        /*@ loop_invariant y == i * x && i <= x;
          @ decreasing x - i;
          @ assignable \nothing;
          @*/
        while (i < x) {
            /*@ ensures y == \before(y) + x;
              @ signals_only \nothing;
              @ assignable \nothing;
              @*/
            {
                y = y + x;
            }
            i = i + 1;
        }
        return y;
    }

    // Automatically provable? Yap. :)
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int add(int x, int y) {
       int z = 0;
       /*@ ensures z == x + y;
         @ diverges false;
         @ signals_only \nothing;
         @ assignable \nothing;
         @*/
       {
           z = x + y;
       }
       return z;
    }

    // :)
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int addWithJump(int x, int y, int z) {
        /*@ requires x >= 0 && y >= 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            label: {
                z = x + y;
                break label;
            }
        }
        return z;
    }

    // :)
    /*@ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int addWithTwoBlockContracts(int x, int y, int z) {
        /*@ requires x >= 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        /*@ also
          @ requires x < 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            z = x + y;
        }
        return z;
    }

    // Not automatically provable, because the contract is not correct
    // and/or the java code is invalid.
    /*@ requires x > 0 && y > 0;
      @ ensures x < y ==> \result == x * y;
      @ ensures x > y ==> \result == x / y;
      @ ensures x == y ==> \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int vonAllemEtwas(int x, int y) {
        int z = 0;
        outside: {
           /*@ requires x > 0 && y > 0;
             @ ensures x == y && z == x + y;
             @ breaks (outside) x < y && z == x * y;
             @ continues (outside) x > y && z == x / y;
             @ returns x == y && z == x + y;
             @ diverges false;
             @ assignable \nothing;
             @*/
            inside: {
                if (x == y && x > 100) {
                    z = x + y;
                    break inside;
                }
                else if (x < y) {
                    z = x * y;
                    break outside;
                }
                else if (x > y) {
                    z = x / y;
                    // Note that the following is not valid java code,
                    // because outside does not label a loop statement.
                    continue outside;
                    while (true) {
                        continue;
                        break;
                        break notALabel;
                    }
                }
                else if (x == y) {
                    return x + y;
                }
            }
        }
        return z;
    }

    /*@ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public void unnecessaryBlockContract() {
        /*@ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            if (true) {
                int i = 1;
            }
        }
    }

    /*@ diverges true;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public void unnecessaryLoopInvariant() {
        /*@ loop_invariant true;
          @*/
        while (true) {
            if (true) {
                int i = 1;
            }
        }
    }

    
    /*@ normal_behavior
      @     ensures     \result != null;
      @     ensures     \fresh(\result);
      @     assignable  \nothing;
      @*/
    public byte[] generateByteArray() {
        int len = getLength();
        /*@ normal_behavior
          @ ensures     len >= 0;
          @ assignable  \nothing;
          @*/
        {len = (len < 0 ? 0 : len);}
        byte[] array = null;
        /*@ normal_behavior
          @ ensures     array != null;
          @ ensures     \fresh(array);
          @ assignable  \nothing;
          @*/
        {array = new byte[len];}
        return array;
    }
    
    /*@ normal_behavior
      @     assignable  \nothing;
      @*/
    private int getLength() {
        return 17;
    }
}
