class Modelfield {
  int x;
  int y;

  //@ model \locset footprint;
  //@ accessible footprint: \empty;

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_1 () {
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_2 () {
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_3 () {
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_4 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_5 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_6 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_7 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_8 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_9 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_10 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }

  //@ requires x > 0;
  //@ requires \disjoint(footprint,\singleton(x));
  //@ ensures x > 0;
  void foo_20 () {
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
    x++; bar();
  }


  //@ ensures true;
  //@ assignable footprint;
  void bar () {};

}
