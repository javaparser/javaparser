class SumAndMax {

    int sum;
    int max;
   
    /*@ public normal_behaviour
      @   requires (\forall int i; 0 <= i && i < a.length; 0 <= a[i]);
      @   assignable sum, max;
      @   ensures (\forall int i; 0 <= i && i < a.length; a[i] <= max);
      @   ensures (a.length > 0
      @           ==> (\exists int i; 0 <= i && i < a.length; max == a[i]));
      @   ensures sum == (\bsum int i; 0; a.length; a[i]);
      @   ensures sum <= a.length * max;
      @*/
    void sumAndMax(int[] a) {
	sum = 0;
	max = 0;
	int k = 0;
      
        /*@ loop_invariant
          @   0 <= k && k <= a.length
          @   && (\forall int i; 0 <= i && i < k; a[i] <= max)
          @   && (k == 0 ==> max == 0)          
          @   && (k > 0 ==> (\exists int i; 0 <= i && i < k; max == a[i]))
          @   && sum == (\bsum int i; 0; k; a[i])
          @   && sum <= k * max;
          @
          @  assignable sum, max;
          @  decreases a.length - k;
          @*/
	while(k <= a.length) {
            if(max < a[k]) {
                max = a[k];
            }
            sum += a[k];
            k++;
	}
    }
}
