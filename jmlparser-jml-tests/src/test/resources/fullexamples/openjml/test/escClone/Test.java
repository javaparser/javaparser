//@ nullable_by_default
public class Test extends A {
    
    public int i;
    
    public void mbyte(/*@ non_null */ byte[] b) {
        byte[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mint(/*@ non_null */ int[] b) {
        int[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mchar(/*@ non_null */ char[] b) {
        char[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mshort(/*@ non_null */ short[] b) {
        short[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mlong(/*@ non_null */ long[] b) {
        long[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }
    
    public void mboolean(/*@ non_null */ boolean[] b) {
        boolean[] bb = b.clone();
        //@ assert i == \old(i);
        //@ assert bb != null;
        //@ assert \fresh(bb);
        //@ assert java.util.Arrays.equalArrays(bb,b);
    }

    // FIXME - add these eventually
//    public void mfloat(/*@ non_null */ float[] b) {
//        float[] bb = b.clone();
//        //@ assert i == \old(i);
//        //@ assert bb != null;
//        //@ assert \fresh(bb);
//        //@ assert java.util.Arrays.equalArrays(bb,b);
//    }
//    
//    public void mdouble(/*@ non_null */ double[] b) {
//        double[] bb = b.clone();
//        //@ assert i == \old(i);
//        //@ assert bb != null;
//        //@ assert \fresh(bb);
//        //@ assert java.util.Arrays.equalArrays(bb,b);
//    }
    
    public void minherited() {
    }
    
    public void mtest() {
        minherited();
        //@ assert i == \old(i);
    }

}

class A {
    
    //@ public normal_behavior
    //@   assignable \nothing;
    public void minherited() {
        
    }
}