public class PreOld {
    
    //@ public normal_behavior a:
    //@  old int y = i + 2;
    //@ also public normal_behavior b:
    //@  old int x = i - 1;
    //@  old int y = i + 1;
    //@ requires x >= 0;
    public void mtest(short i) {
        //@ assert i - 1 == \old(x,a);
    }
    
}