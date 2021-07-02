class ForReferenceArray {

  // This example has been refactored pending solution to bug #1288

  //@ ensures true;
  void foo(Object[] as) {
    //@ maintaining 0 <= \index && \index <= as.length; 
    //@ decreasing as.length-\index;
    //@ assignable \strictly_nothing;
    for (Object a: as) ;
  }
}
