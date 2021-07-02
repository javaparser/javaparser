class AccessChain4 {
  AccessChain4 a;
  int x;
  int y;


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_1 () {
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_2 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_3 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_4 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_5 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_6 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_7 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_8 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_9 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_10 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ requires a != null && a.a != null && a.a.a != null && a.a.a.a != null;
  //@ requires a.a.a.a.x > 0;
  //@ ensures a.a.a.a.x > 0;
  void foo_20 () {
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
    a.a.a.a.x++; bar();
  }


  //@ ensures true;
  //@ assignable y;
  void bar () {};

}
