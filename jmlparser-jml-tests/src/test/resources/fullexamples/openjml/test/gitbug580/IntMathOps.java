/**
 * @overview
 *
 * @author dmle
 *
 * @version
 */
public class IntMathOps {
   /*@ public normal_behavior
     @ requires y >= 0;
     @ assignable \nothing;
     @ ensures 0 <= \result
     @         && \result * \result <= y
     @         && ((0 <= (\result + 1) * (\result + 1))
     @            ==> y < (\result + 1) * (\result + 1));
     @*/
  public static int isqrt(int y) {
	  double d = y;
	  //@ assert Double.isFinite(d) && y >= 0;
	  double sd = Math.sqrt(d);
      //@ assert Math.close(d, sd*sd, 2.0E-6);
	  //@ assert sd >= 0;
	  int sy = (int) sd;
	  //@ assert sy >= 0;
	  //@ assert sy <= sd < sy+1;
	  //@ assert sy*sy <= sd*sd < (sy+1)*(sy+1);
	  return sy;
  }
  
  /*
  public static int isqrt(int y) {
    return (int) Math.sqrt(y);
  }
   */
}
