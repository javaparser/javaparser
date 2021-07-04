public class Test {
    
    public static class T {}
    
    //@ public normal_behavior
    //@   ensures true;
    public T m() {
        
        return new T();
    }
}
// Default constructors should have just normal pure behavior