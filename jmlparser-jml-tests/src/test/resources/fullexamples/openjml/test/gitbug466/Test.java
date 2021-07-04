public class Test {
    /*@ public normal_behavior
      @   ensures \result == 7;
      @*/
    public int run(Bottom b) {
        int i = b.other();
        //@ assert i == 4;
        int j = b.identifier();
        //@ assert j == 3;

        return i + j;
    }   
}