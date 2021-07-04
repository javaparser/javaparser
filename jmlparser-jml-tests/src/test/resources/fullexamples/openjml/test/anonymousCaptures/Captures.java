//@ non_null_by_default
public class Captures {
    
    public void m(int x) {
        int y = x;
    
        AAA a = new AAA() { 
            //@ public invariant x == y;
            
            //@ also public normal_behavior
            //@   ensures \result == (x == y); 
            //@ pure
            public boolean p() { return x == y; } 
            };
        boolean res = a.p();
        //@ assert res;
    }
        
    public void mm(/*@ nullable */ Object xxxx) {
    
        // @ assert xxxx != null;
        AAA a = new AAA() { 
            //@ public invariant xxxx != null;
            
            //@ also public normal_behavior
            //@ ensures \result == (xxxx != null);  
            //@ pure
            public boolean p() { return xxxx != null; } 
            };
        boolean res = a.p();
        // @ assert res;
    }
    
}

class AAA {
    
    int z;
    
    //@ public normal_behavior
    //@ pure
    public AAA() { z = 424242; }
    
    //@ public normal_behavior
    //@ pure
    public boolean p() { return false; }
}