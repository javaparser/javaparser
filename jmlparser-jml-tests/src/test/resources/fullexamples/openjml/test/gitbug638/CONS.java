public class CONS {

public int x;

//@ public normal_behavior
//@   ensures \result == x;
//@ pure helper
public int size() { return x;}

//@ public normal_behavior
//@   requires y == 10;
//@   requires x == 10;
//@ also
//@ public exceptional_behavior
//@ requires size() != 10;
public  CONS(int y) { x = y; if ( y != 10) throw new RuntimeException(); }

}
 
