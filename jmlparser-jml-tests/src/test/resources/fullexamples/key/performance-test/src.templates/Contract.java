class Contract {
  int x;
  int y;


  //@ requires x > 0;
  //@ ensures x > 0;
  void foo () {
    x++; bar();
  }


  //@ ensures true;
  //@ assignable y;
  void bar () {};

}
