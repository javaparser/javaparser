public class Weird {

    // Not provable. But demonstrates usage of different behaviors.
    /*@ ensures x > 0 && y > 0 ==> \result == x + y;
      @ ensures x < 0 && y > 0 ==> \result == x / y;
      @ ensures x > 0 && y < 0 ==> \result == x % y;
      @ ensures x < 0 && y < 0 ==> \result == x * y;
      @ signals (Exception e) x == 0 && y == 0;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int behaviors(int x, int y) {
        int z = 0;
        outside: {
            /*@ normal_behavior
              @ requires x > 0 && y > 0;
              @ ensures z == x + y;
              @ assignable \nothing;
              @
              @ also
              @
              @ break_behavior
              @ requires x < 0 && y > 0;
              @ breaks (outside) z == x / y;
              @ assignable \nothing;
              @
              @ also
              @
              @ continue_behavior
              @ requires x > 0 && y < 0;
              @ continues () z == x % y;
              @ assignable \nothing;
              @
              @ also
              @
              @ return_behavior
              @ requires x < 0 && y < 0;
              @ returns \result == x * y;
              @ assignable \nothing;
              @
              @ also
              @
              @ exceptional_behavior
              @ requires x == 0 && y == 0;
              @ signals (Exception e) z == 0;
              @ assignable \nothing;
              @*/
           {
               if (x > 0 && y > 0) {
                   z = x + y;
               }
               if (x < 0 && y > 0) {
                   z = x / y;
                   break outside;
               }
               if (x > 0 && y < 0) {
                   z = x % y;
                   // Note that this is incorrect java code, because there is no loop statement.
                   continue;
               }
               if (x < 0 && y < 0) {
                   return x * y;
               }
               if (x == 0 && y == 0) {
                   z = 0;
                   throw new RuntimeException("foo");
               }
           }
        }
        return z;
    }

    // Not provable.
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @
      @ also
      @
      @ requires x < 0 && y < 0;
      @ ensures \result == x * y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @
      @ also
      @
      @ requires x < 0 && y > 0;
      @ ensures \result == x / y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int multipleBlockContracts(int x, int y) {
        int z = 0;
        outside: {
            /*@ requires x >= 0 && y >= 0;
              @ ensures z == x + y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @
              @ also
              @
              @ requires x < 0 && y < 0;
              @ returns \result == x * y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @
              @ also
              @
              @ requires x < 0 && y > 0;
              @ breaks (outside) z == x / y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @*/
           {
               if (x >= 0 && y >= 0) {
                   z = x + y;
               }
               if (x < 0 && y < 0) {
                   return x * y;
               }
               while (true) {
                   if (x < 0 && y >= 0) {
                       z = x / y;
                       break label;
                   }
                   else {
                       continue;
                   }
               }
           }
        }
        return z;
    }

    // Not provable.
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int bar(int x, int y) {
        int z = 0;
        label: {
            /*@ requires x > 0 && y > 0;
              @ ensures z == \before(z);
              @ breaks (label) z < \before(z);
              @ continues () z > \before(z);
              @ returns z + \before(z) == 0 && \result == 100;
              @ diverges x == y;
              @ signals (Exception e) \before(z) - z == 0;
              @ assignable \nothing;
              @ assignable \nothing;
              @*/
           {
               if (x > 0 && y > 0) {
                   z = x + y;
               }
               if (x < 0 && y > 0) {
                   z = x / y;
                   break label;
               }
               if (x > 0 && y < 0) {
                   z = x % y;
                   continue;
               }
               if (x < 0 && y < 0) {
                   return x * y;
               }
               if (x == 0 && y == 0) {
                   z = 0;
                   throw new RuntimeException("foo");
               }
           }
        }
        return z;
    }

    // I used this to test variable renaming done by ProgVarReplacer.
    // Expand method 'ta'.
    /*@ diverges false;
      @*/
    public int go(int x, int y) {
        int z = 0;
        /*@ requires z == 0;
          @ ensures x == y;
          @ breaks () x > y;
          @ continues () x < y;
          @ returns x == 0 && y == 0;
          @ signals (Exception e) x + y == 0;
          @ diverges x == y;
          @ assignable \nothing;
          @*/
        {
            if (x > 0) {
                ta(z, x, 3);
            }
        }
    }

    public void ta(int u, int v, int w) {
        int x = 1;
        /*@ requires x == 0;
          @ ensures u == v;
          @ breaks () v > w;
          @ continues () w < v;
          @ returns v == 0 && u == 0;
          @ signals (Exception e) x + u == 0;
          @ diverges x == u;
          @ assignable \nothing;
          @*/
        {
            if (u > 0) {
                x = v + w;
            }
        }
    }

}
