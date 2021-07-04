public interface TestC {
    
    //@   requires r >= 5;
    //@   {|
    //@   requires r >= 10;
    //@   requires r >= 20;
    //@ also
    //@   requires r >= 15;
    //@   requires r >= 25;
    //@   |}
    public void m( /*@ non_null */Integer p, int q,  /*@ non_null */Integer r);

}