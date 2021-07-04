public class trace {
    
    public void mnonnullelements(int[] a) {
        int i = 0;
        //@ assert i == 0 && \nonnullelements(a);
        return ;
    }
    
    public void mnotmodified(int i) {
        //@ assert \not_modified(i);
        i = 4;
        //@ assert i == 4 && \not_modified(i);
        return ;
    }
}