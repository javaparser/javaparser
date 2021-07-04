public class Test{
    
    //@ public normal_behavior
    //@   requires true;
    //@   requires System.out.isOpen;
    public void m(java.util.Optional<Throwable> exception) {
        
        exception.ifPresent( x-> x.printStackTrace(System.out));
    }
}