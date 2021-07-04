public class MyClass {
    //@ public normal_behavior
    public static void main(String args[]){
        int i = 0;
        try {
          //@ loop_invariant i == 0;
          while (i < 5) {
            i++;
            throw new Exception();
          }
          //@ unreachable;
        } catch (Exception e) { }
        //@ assert i == 1;
    }
}