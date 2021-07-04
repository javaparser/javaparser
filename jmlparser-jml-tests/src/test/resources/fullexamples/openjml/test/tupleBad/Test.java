public class Test {
    
    public void m(String e) {
        //@ ghost int t = (1,e,4). 1;
        //@ ghost int v = (1,e,4).3;
        //@ set (t,v) = (2,3);
        //@ set (t,v) = (2,e);
        //@ set (t,v) = (e,e);
        //@ set (t,v) = (2,3,4);
        //@ set (t,v) = 2;
        //@ ghost Integer w = (1,e,4).2;
        //@ ghost String s;
        //@ ghost Boolean ss;
        //@ set (t,ss,w,s) = 2;
        //@ set v = (1,e,4).0;
        //@ set v = (1,e,4).4;
        //@ set v = (1,e,4).a;
        //@ set v = e.4;
    }
    
}