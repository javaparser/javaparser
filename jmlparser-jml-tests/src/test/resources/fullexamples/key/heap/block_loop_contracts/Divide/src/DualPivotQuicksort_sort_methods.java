
public class DualPivotQuicksort_sort_methods {

    static int less, great;
    static int e1,e2,e3,e4,e5;
    
    /*@
      @ normal_behaviour
      @ requires 0 <= left && left < right && right - left >= 46 && right < a.length;
      @ requires a.length > 46;
      @ requires (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
      @ requires (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
      @ ensures a[e1] <= a[e2] && a[e2] <= a[e3] && a[e3] <= a[e4] && a[e4] <= a[e5];
      @ ensures left < e1 && e1 < e2 && e2 < e3 && e3 < e4 && e4 < e5 && e5 < right;
      @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
      @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
      @ assignable e1,e2,e3,e4,e5, a[left..right];
      @*/ 
    static void prepare_indices(int[] a, int left, int right) {
        {calcE(left, right);}
        eInsertionSort(a,left,right,e1,e2,e3,e4,e5); 
    }
    
    /*@
      @ normal_behaviour
      @ requires 0 <= left && left < right && right - left >= 46;
      @ ensures left < e1 && e1 < e2 && e2 < e3 && e3 < e4 && e4 < e5 && e5 < right;
      @ assignable e1,e2,e3,e4,e5;
      @*/ 
    static void calcE(int left, int right) {
        int length = right - left + 1;
        int seventh = (length / 8) + (length / 64) + 1;
        e3 = (left + right) / 2; // The midpoint
        e2 = e3 - seventh;
        e1 = e2 - seventh;
        e4 = e3 + seventh;
        e5 = e4 + seventh;
    }

    /*@
      @ normal_behaviour
      @ requires a.length > 46;
      @ requires 0 <= left && left < e1 && e5 < right && right < a.length;
      @ requires left < e1 && e1 < e2 && e2 < e3 && e3 < e4 && e4 < e5 && e5 < right;
      @ requires (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
      @ requires (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
      @ ensures a[e1] <= a[e2] && a[e2] <= a[e3] && a[e3] <= a[e4] && a[e4] <= a[e5];
      @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
      @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
      @ assignable a[left..right];
      @*/ 
    static void eInsertionSort(int[] a, int left, int right, int e1, int e2, int e3, int e4, int e5) {
        /*@
          @ ensures (a[e1] <= a[e2]);
          @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
          @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
          @ assignable a[e1], a[e2];
          @ signals_only \nothing;
          @*/
        {
            if (a[e2] < a[e1]) { int t = a[e2]; a[e2] = a[e1]; a[e1] = t; }
        }

        /*@
          @ ensures (a[e1] <= a[e2] && a[e2] <= a[e3]);
          @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
          @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
          @ assignable a[e1], a[e2], a[e3];
          @ signals_only \nothing;
          @*/
        {
            if (a[e3] < a[e2]) { int t = a[e3]; a[e3] = a[e2]; a[e2] = t;
            if (t < a[e1]) { a[e2] = a[e1]; a[e1] = t; }
            }}

        /*@
          @ ensures (a[e1] <= a[e2] && a[e2] <= a[e3] && a[e3] <= a[e4]);
          @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
          @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
          @ assignable a[e1], a[e2], a[e3], a[e4];
          @ signals_only \nothing;
          @*/
        {
            if (a[e4] < a[e3]) { int t = a[e4]; a[e4] = a[e3]; a[e3] = t;
            if (t < a[e2]) { a[e3] = a[e2]; a[e2] = t;
            if (t < a[e1]) { a[e2] = a[e1]; a[e1] = t; }
            }
            }}

        /*@
          @ ensures (a[e1] <= a[e2] && a[e2] <= a[e3] && a[e3] <= a[e4] && a[e4] <= a[e5]);
          @ ensures (\forall int i; 0 <= i && i < left; (\forall int j; left <= j && j < a.length; a[i] <= a[j])); 
          @ ensures (\forall int i; 0 <= i && i <= right; (\forall int j; right < j && j < a.length; a[i] <= a[j]));
          @ assignable a[e1], a[e2], a[e3], a[e4], a[e5];
          @ signals_only \nothing;
          @*/
        {
            if (a[e5] < a[e4]) { int t = a[e5]; a[e5] = a[e4]; a[e4] = t;
            if (t < a[e3]) { a[e4] = a[e3]; a[e3] = t;
            if (t < a[e2]) { a[e3] = a[e2]; a[e2] = t;
            if (t < a[e1]) { a[e2] = a[e1]; a[e1] = t; }
            }
            }
            }}
    }
}
