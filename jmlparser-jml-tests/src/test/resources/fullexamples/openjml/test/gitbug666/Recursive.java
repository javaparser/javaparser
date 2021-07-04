public class Recursive {

   //@ public normal_behavior
   //@   requires y >= 0;
   //@   requires x + y <= Integer.MAX_VALUE;
   //@   ensures \result == x + y;
   //@ pure
   public static int add(int x, int y) {
       return y == 0 ? x : add(x+1,y-1);
   }

   //@ public normal_behavior
   //@   requires y >= 0;
   //@   requires x >= 0;
   //@   requires x * y <= Integer.MAX_VALUE;
   //@   ensures \result == x * y;
   //@ pure
   public static int mult(int x, int y) {
       return y == 0 ? 0 : x + mult(x,y-1);
   }

   //@ public normal_behavior
   //@   requires x <= 10 && y <= 15;
   //@   requires y >= 0 && x >= 1;
   //@   ensures \result == (y == 0 ? 1 : y == 1 ? x : x * mpow(x,y-1));
   //@ pure
   //@ model public static function helper long mpow(long x, long y);

   //@ public normal_behavior
   //@   requires x <= 10 && y <= 15;
   //@   requires y >= 0 && x >= 1;
   //@   ensures (\lbl R \result) == (long)(\lbl MP mpow(x,y));
   //@ pure
   public static long pow(long x, long y) {
       //@ show x, y;
        return y == 0 ? 1 : y == 1 ? x : x * pow(x, y-1);
   }
}
