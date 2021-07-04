public class Test {
    
    //@ ensures \result >= 0;
    public static int main(String ... args) {
        return args.length;
    }
    
}

// Propblem reported is that this is not the externally-invokable main
// method because it is not void. However, Java allows this.
// Going to let this be as whether or not to issue a warning is more a
// Java issue than JML.