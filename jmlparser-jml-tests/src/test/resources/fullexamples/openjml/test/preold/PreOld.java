public class PreOld {
    
    //@ public normal_behavior a:
    //@  old int y = i + 2;
    //@ also public normal_behavior b:
    //@ old int x = i - 1;
    //@ old int y = i + 1;
    //@ requires x >= 0;
    public void mtest(short i) {
        //@ assert i - 1 == \old(x,b);
        //@ assert \old(y,b) == i + 1;
        //@ assert \old(y,a) == i + 2;
    }
    
    //@ public normal_behavior a:
    //@   requires b;
    //@   old int x = i + 1;
    //@ also public normal_behavior b:
    //@   requires !b;
    //@   old int x = i -1;
    public void mbad(boolean b, int i) {
        //@ assert \old(x,a) == i + 1;
        //@ assert \old(x,b) == i - 1;
    }
    
    //@ public normal_behavior a:
    //@   requires b;
    //@   old int x = i + 1;
    //@ also public normal_behavior b:
    //@   requires !b;
    //@   old int x = i -1;
    public void mok(boolean b, int i) {
        if (b) {
            //@ assert \old(x,a) == i + 1;
        } else {
            //@ assert \old(x,b) == i - 1;
        }
    }
    //@ public normal_behavior a:
    //@   requires b;
    //@   old int x = i + 1;
    //@ also public normal_behavior b:
    //@   requires !b;
    //@   old int x = i -1;
    public void mbad2(boolean b, int i) {
        if (!b) {
            //@ assert \old(x,a) == i + 1;
        } else {
            //@ assert \old(x,b) == i - 1;
        }
    }
}