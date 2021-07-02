class Assert {

    /*@ normal_behavior
      @ ensures \result.length == x*x;
      @*/
    int[] createArray (int x) {
        final int z = x*x;
        //@ assert z >= 0;
        { int y; } // workaround bug #1261
        return new int[z];
    }
}
