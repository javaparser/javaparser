public class Test2 {
    
    public void m(String e) {
        //@ ghost int t = 1;
        //@ ghost int v = 2;
        //@ set (t,v) = (v+10,t+20);
        //@ assert t == 12;
        //@ assert v == 21;
        
        //@ set (t,v) = t+10;
        //@ assert t == 22;
        //@ assert v == 22;

    }
    
}