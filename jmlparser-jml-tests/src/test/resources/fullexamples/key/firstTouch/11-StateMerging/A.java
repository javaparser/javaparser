class A {

   //@ ensures \result > 0;
   int f() { return 42; }

   //@ ensures \result != null;
   Object g() { return this; }

   //@ ensures \result;
   boolean m(boolean b) {
       boolean r;
       if(b) {
           r = f() > 0;
       } else {
           r = g() != null;
       }
       
       //@ merge_point;
       
       return r;
   }
}

