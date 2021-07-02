public class Test {
    
    int a;
    int b;
    
    /*@ public normal_behavior
      @ requires a == b;
      @ requires a == 42;
      @ ensures \old(b) == 42;
      @*/
    public void test_attr() { }

    /*@ public normal_behavior
      @ requires a == b;
      @ requires a == 42;
      @ ensures \old(b) == 42;
      @*/
    public void test_arg(int a, int b) { }
    
    /*@ public normal_behavior
      @ requires b || !b;
      @*/
    public void test2(boolean b) { }
    
    /*@ public normal_behavior
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable \nothing;
      @*/
    public int sum(int[] arr) {
        int i = 0;
        int result = 0;
        
        // The range check (loop_invariant 0 <= i && i <= arr.length) is intentionally missing.
        /*@ loop_invariant result == (\sum int j; 0 <= j && j < i; arr[i]);
          @ decreases arr.length - i;
          @ assignable \nothing;
          @*/
        while (i < arr.length) {
            result += arr[i];
            ++i;
        }
        
        return result;
    }
    
    // This contract contains an intentional mistake.
    /*@ public normal_behavior
      @ requires x <= 0;
      @ ensures \result > 0;
      @*/
    public int very_simple(int x){
        if(x > 0) {
            x--;
        } else {
            x++;
        }
        return ++x;
    }
}
