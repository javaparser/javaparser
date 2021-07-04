public class Test {
    
    //@ requires e != null;
    public void m(TestEnum.EE e) {
        //@ assert e == TestEnum.EE.AA | e == TestEnum.EE.BB;
        //@ assert TestEnum.EE.AA != TestEnum.EE.BB;
        //@ assert \distinct(TestEnum.EE.AA, TestEnum.EE.BB, null);
    }
}