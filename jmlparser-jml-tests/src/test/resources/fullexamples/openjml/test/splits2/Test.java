public class Test {

    //@ requires k >= 0;
    public void whok(int k) {
        int i = k;
        //@ loop_invariant 0 <= i <= k;
        //@ loop_invariant \index == k-i;
        //@ split
        while (i > 0) {
            i --;
        }
        //@ assert i == 0;
    }
    
    
    public void wh(int i) {
        //@ split
        if (i < 0) {
            //@ assert i < -1; // Split A
            return;
        }
        int j = i;
        //@ loop_invariant -1 <= j <= i;
        //@ split
        while (j >= 0) {
            --j;
            //@ loop_invariant 0 <= k <= 10;
            //@ split
            for (int k=0; k<10; k++) {
                //@ assert k < 0; // FAILS - BAA
            }
            
            int[] a = {1,2,3};
            //@ split
            for (int k: a) {
                //@ assert i < 1; // FAILS - BABA
            }
            
            //@ assert i < 2; // FAILS - BABB
        }
        
        //@ loop_invariant 0 <= j <= 10;
        //@ split
        while (j < 10) {
            j++;
            //@ assert i < 3; // FAILS - BBA
        }
        //@ assert j < 0; // FAILS - BBB
    }

    //@ requires k >= 0;
    public void whfor(int k) {
        int j = 0;
        //@ loop_invariant 0 <= i <= k;
        //@ loop_invariant j == k-i;
        //@ loop_invariant \index == k-i;
        //@ split
        for (int i = k; i > 0; i--) {
            j++;
        }
        //@ assert j == k;
    }
    
    public void enfor(int[] k) {
        int j = 0;
        //@ loop_invariant j == \count;
        //@ loop_invariant 0 <= \count <= k.length;
        //@ loop_writes j;
        //@ split
        for (int i: k) {
            j++;
        }
        //@ show j, k.length;
        //@ assert j == k.length;
    }
    

}