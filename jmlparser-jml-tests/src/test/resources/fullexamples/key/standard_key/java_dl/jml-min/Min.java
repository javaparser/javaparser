class Min {

  //@ ensures (\min int x; x > 40; x+1) == 42;
  void bar(){}

  //@ ensures (\min int x; false; 42) == 42;
  void foo(){} 

  //@ ensures (\min int x; false; 42) != 42;
  void foo2(){} 
}
