final class List {

    final int max;
    final int[] a;
    int p;


    /*@
      @ public normal_behaviour
      @   requires (\forall int i; 0<=i && i < array.length; array[i] >= 0);
      @   ensures this.a == array;
      @   ensures this.p == 0;
      @   assignable this.*;
      @*/
    List(int[] array) {
        this.a = array;
        this.p = 0;
        int tmp = 0;

	/*@ maintaining 0<=i && i<=a.length &&
	  @  (\forall int k; 0<=k && k<i; tmp >= array[k]);
	  @ decreases a.length - i;
	  @ assignable \nothing;
	  @*/
        for(int i = 0; i < a.length; i++) {
            if(array[i] > tmp) {
                tmp = array[i];
            }
        }

        max = tmp;
    }
    
    //@ public invariant 0 <= p && p <= a.length;
    //@ public invariant a != null;
    //@ public invariant (\forall int i; 0<=i && i < a.length; max >= a[i]);
    //@ public invariant (\forall int i; 0<=i && i < a.length; a[i] >= 0);

    //@ accessible <inv> : this.*, this.a[*];
    
    //@ pure
    boolean isEmpty() {
        return p == a.length;
    }
    
    //@ pure
    int head() {
        return a[p];
    }
    
    /*@ requires p < a.length;
      @ ensures p == \old(p) + 1;
      @ assignable p;
      @*/
    int pop() {
        return a[p++];
    }
}