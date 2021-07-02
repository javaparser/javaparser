class Test {

  static RuntimeException e;
  int x = 4;
  int y;
  int w;

  //@ invariant x == 4 && w == 0;
  //@ requires e != null;
  //@ signals (Exception) y == z;
  //@ signals_only RuntimeException;
  Test (int z) {
      y = z;
      throw e;
  }

}

