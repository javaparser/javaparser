public class B {
    //@ public normal_behavior
    //@   ensures true;
    public static void caller() {
        Inner a = new Inner();
    }
    
    public static class Inner {
        //@ private normal_behavior
        //@   ensures true;
        //@ pure
        private Inner() {
        }
    }
}
