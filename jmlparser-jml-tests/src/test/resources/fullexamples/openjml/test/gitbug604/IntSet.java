//@ model import org.jmlspecs.lang.JMLDataGroup;

public interface IntSet {
    //@ public instance model JMLDataGroup state;
    
    public /*@ pure @*/ boolean contains(int i);

    //@ requires size() > 0;
    //@ assignable state;
    //@ ensures contains(\result);
    public int pick();

    //@ assignable state;
    //@ ensures contains(i);
    //@ ensures size() >= \old(size());
    public void add(int i);

    //@ assignable state;
    //@ ensures !contains(i) && size() <= \old(size());
    public void remove(int i);

    //@ ensures \result >= 0;
    public /*@ pure @*/ long size();
}
