public class Test {
    
    //@ requires i == 0;
    //@ signals (RuntimeException) false; // SHOULD FAIL
    public void m0(int i, RuntimeException e) {
        A: {
           try {
               if (i == 0) throw e;
           } finally {
               if ( i == 0) i = 1;
           }
        }
        //@ reachable; // ERROR
    }
    
    //@ requires i == 0;
    //@ signals (RuntimeException) false;
    public void m1(int i, RuntimeException e) {
        A: {
           try {
               if (i == 0) throw e;
           } finally {
               if ( i == 0) break A;
           }
        }
        //@ reachable;
    }
    
    //@ requires i == 0;
    //@ signals (RuntimeException) false;
    public void m2(int i, RuntimeException e) {
        while (true) {
           try {
               if (i == 0) throw e;
           } finally {
               if ( i == 0) break;
           }
        }
        //@ reachable;
    }
    
    //@ requires i == 0;
    //@ signals (RuntimeException) false;
    public void m3(int i, RuntimeException e) {
        switch (i) {
           default:
           try {
               if (i == 0) throw e;
           } finally {
               if ( i == 0) break;
           }
        }
        //@ reachable;
    }
    
    
    //@ requires i == 0;
    //@ signals (RuntimeException) false;
    public void m4(int i, RuntimeException e) {
        while (i<5) {
           try {
               if (i < 10) throw e;
           } finally {
               i++;
               if ( i < 10) break;
           }
        }
        //@ reachable;
    }

}