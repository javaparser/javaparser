class Dynamic2 {
  int x;
  int y;

  //@ model \locset rep;
  //@ accessible rep: rep;

  //@ model \locset rep2;
  //@ accessible rep2: rep2;

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_1 () {
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_2 () {
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_3 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_4 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_5 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_6 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_7 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_8 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_9 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_10 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ requires x > 0 & y > 0;
  //@ requires \subset(\locset(x, y), rep);
  //@ requires \disjoint(rep, rep2);
  //@ ensures x > 0 & y > 0;
  void foo_20 () {
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
    x++; y++; bar();
  }

  //@ ensures \new_elems_fresh(rep2);
  //@ assignable rep2;
  void bar () {};

}
