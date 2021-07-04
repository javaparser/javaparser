public class trace {
    
    public void m() {
        int j = 0;
        //@ loop_invariant 0 <= i && i <= 10;
        //@ loop_invariant i == j;
        //@ decreases 10-i;
        for (int i=0; i<10; i++) {
            j = j + (i==5 ? 2 : 1);
        }
    }

    public void mok() {
        int j = 0;
        //@ loop_invariant 0 <= i && i <= 10;
        //@ loop_invariant i == j;
        //@ loop_invariant i == \count;
        //@ decreases 9-i;
        for (int i=0; i<10; i++) {
            j = j + 1;
        }
    }

    public void mdec() {
        int j = 0;
        //@ loop_invariant 0 <= i && i <= 10;
        //@ loop_invariant i == j;
        //@ decreases 8-i;
        for (int i=0; i<10; i++) {
            j = j + 1;
        }
    }

}