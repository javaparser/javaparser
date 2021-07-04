public class trace {
    
    public void mgood() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }
    public void m1() {
        int k = 5;
        int j = 1;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }
    public void m2() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        for (int i=0; i<k; i++) {
            ++j;
            if (j == 3) {
                //@ assert false;
            }
        }
        //@ assert j == k;
        return ;
    }
    public void m3() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        //@ decreases j;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }
    public void m4() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        //@ decreases i-j;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }
    public void m5() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        //@ decreases k-j-1;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }

    public void m6() {
        int k = 5;
        int j = 0;
        //@ loop_invariant j == i && 0 <= i && i <= k;
        //@ decreases k-j-2;
        for (int i=0; i<k; i++) {
            ++j;
        }
        //@ assert j == k;
        return ;
    }

    public void mwhile() {
        int k = 5;
        int j = 0;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i <= k;
        while (i < k) {
            j += 2;
            ++i;
        }
        //@ assert j == k+k;
        return ;
    }
    public void mwhile1() {
        int k = 5;
        int j = 1;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i <= k;
        while (i < k) {
            j += 2;
            ++i;
        }
        //@ assert j == k+k;
        return ;
    }
    public void mwhile2() {
        int k = 5;
        int j = 0;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i <= k;
        while (i < k) {
            j += 3;
            ++i;
        }
        //@ assert j == k+k;
        return ;
    }
    
    public void mdo() {
        int k = 5;
        int j = 0;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i < k;
        //@ decreases k-i;
        do {
            j += 2;
            ++i;
        } while (i < k);
        //@ assert j == k+k;
        return ;
    }
    
    public void mdo1() {
        int k = 5;
        int j = 1;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i < k;
        do {
            j += 2;
            ++i;
        } while (i < k);
        //@ assert j == k+k;
        return ;
    }
    
    public void mdo2() {
        int k = 5;
        int j = 0;
        int i = 0;
        //@ loop_invariant j == 2*i && 0 <= i && i < k;
        do {
            j += 3;
            ++i;
        } while (i < k);
        //@ assert j == k+k;
        return ;
    }

    public void mforeach(int[] a) {
        int j = 0;
        //@ loop_invariant j == \count && 0 <= \count && \count <= a.length;
        for (int i: a) {
            j += 1;
        }
        //@ assert j == a.length;
        return ;
    }
    public void mforeach1(int[] a) {
        int j = 0;
        //@ loop_invariant j == 0 && 0 <= \count && \count <= a.length;
        for (int i: a) {
            j += 1;
        }
        //@ assert j == a.length;
        return ;
    }
    public void mforeach2(int[] a) {
        int j = 0;
        //@ loop_invariant j == \count && 0 <= \count && \count <= a.length;
        for (int i: a) {
            j = j + j + 1;
        }
        return ;
    }
    public void mforeach3(int[] a) {
        int j = 0;
        //@ loop_invariant j == \count && 0 <= \count && \count <= a.length;
        //@ decreases a.length - j;
        for (int i: a) {
            j += 1;
        }
        //@ assert j == a.length;
        return ;
    }
    public void mforeach4(int[] a) {
        int j = 0;
        //@ loop_invariant j == \count && 0 <= \count && \count <= a.length;
        //@ decreases j;
        for (int i: a) {
            j += 1;
        }
        //@ assert j == a.length;
        return ;
    }
    public void mforeach5(int[] a) {
        int j = 0;
        //@ loop_invariant j == \count && 0 <= \count && \count <= a.length;
        //@ decreases -j;
        for (int i: a) {
            j += 1;
        }
        //@ assert j == a.length;
        return ;
    }

}