//@ non_null_by_default
public class Test implements IFace {
    
    public void m() {
        
        //@ assert get() == 1;
        //@ assert getd() == 2;
    }
    
}

interface IFace {
    
    //@ ensures \result == 1;
    //@ model public pure int get();
    
    //@ ensures \result == 2;
    //@ model public pure int getd();
}

/* Oddities: TYhis example fails if only get is present. But it succeeds in finding get if getd (which is declqared as defaiult)
if present. If getd is not default, neither is found.

*/