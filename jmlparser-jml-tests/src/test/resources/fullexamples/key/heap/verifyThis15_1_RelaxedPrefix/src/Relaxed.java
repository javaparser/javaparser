public class Relaxed {


    /*@ requires 0 < pat.length && pat.length <= a.length;
      @ ensures \result <= pat.length;
      @ ensures \result >= 0 <==> (
      @            (\forall int j; 0 <= j < \result; pat[j] == a[j])
      @         && (\forall int j; \result < j < pat.length; pat[j] == a[j-1])
      @         );
      @*/ 
    public static int isRelaxedPrefix(int[] pat, int[] a) {
        int shift = 0;
        int k = pat.length;

        /*@ maintaining pat.length <= a.length;
          @ maintaining 0 <= i && i <= pat.length;
          @ maintaining 0 <= i-shift && i-shift <= a.length;
          @ maintaining shift == 0 || shift == 1;
          @ maintaining 0 <= k < i || k == pat.length;
          @ maintaining shift == 1 <==> 0 <= k < pat.length;
          @ maintaining shift == 0 <==> k == pat.length;
          @ maintaining (\forall int j; 0 <= j < k && j < i; pat[j] == a[j]);
          @ maintaining (\forall int j; k < j < i; pat[j] == a[j-1]);
          @ decreasing pat.length-i;
          @ assignable \strictly_nothing;
          @*/ 
        for(int i=0; i<pat.length; i++) {
            if (pat[i]!=a[i-shift]) 
                if (shift==0) {
                    k = i;
                    shift=1;
                }
                    else return -1;
        }
        return k;
    }

}

