
public class TestTest {
    public void test(){
        Test t = new Test();
       
        int a = t.getb();
        //@ assert a ==1;  // result of geta() is 0 so result of getb() should be 1 and assertion should pass.
    }
}


class Test {
   
    public Test(){
       
    }
   /*@  public normal_behavior
    @     ensures \result == 0;  // postcond 1  // incorrect postCondition
    @*/
    public /*@ pure @*/ int geta(){
        return 1;
    }
   
    /*@  public normal_behavior
    @     ensures \result == geta() + 1;   // postcond 2
    @*/
    public int getb(){
        return geta() +1;
    }

}
