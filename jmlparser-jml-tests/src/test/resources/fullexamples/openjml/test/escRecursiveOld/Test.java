public class Test {
    
    //@ old int nnnn = 120+4;
    //@ ensures \result <= nnnn;
    public int m(int n) {
        if (n == 0) return 124;
        return m(n-1);
    }
}
// Tests the fix to a problem when a method with old clauses
// is called recursively.