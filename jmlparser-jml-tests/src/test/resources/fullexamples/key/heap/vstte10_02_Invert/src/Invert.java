class Invert {

   /*@ public normal_behaviour
     @   requires a != b;
     @   requires a.length == b.length;
     @   requires (\forall int x; 0 <= x && x < a.length; 0 <= a[x] && a[x] < a.length);
     @   requires (\forall int x, y; 0 <= x && x < y && y < a.length; a[x] != a[y]);
     @   requires (\forall int q; 0 <= q && q < a.length; (\exists int w; 0 <= w && w < a.length; a[w] == q));
     @ 
     @   assignable b[*];
     @                 
     @   ensures (\forall int x, y; 0 <= x && x < y && y < b.length; b[x] != b[y]);
     @   ensures (\forall int x; 0 <= x && x < b.length; b[a[x]] == x);
     @*/
   public static void invert(int[] a, int[] b) {
       
       /*@ loop_invariant 0 <= i && i <= a.length 
         @    && (\forall int x; 0 <= x && x < i; b[a[x]] == x);
         @  assignable b[*];
         @  decreases a.length - i;
         @*/
       for(int i = 0; i < a.length; i++) {
           b[a[i]] = i;
       }
   }
}
