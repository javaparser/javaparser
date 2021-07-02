class Recursion {
   int x;

   // this might be a user input ...
   /*@ normal_behaviour
     @  assignable x;
     @*/
   int arbNumber();

   /*@ normal_behaviour
     @  measured_by 1, n;
     @*/
   void f(int n) {
      if(n > 0) f(n-1);
      g(arbNumber());
   }

   /*@ normal_behaviour
     @  measured_by 0, m;
     @*/
   void g(int m) {
      if(m > 0) g(m-1);
   }
}
