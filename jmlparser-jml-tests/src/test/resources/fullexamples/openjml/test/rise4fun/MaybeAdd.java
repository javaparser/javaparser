// Can you spot the two errors
// in this program?

public class MaybeAdd {
    //@ requires a > 0;
    //@ requires b > 0;
    //@ ensures \result == a+b;
    public /*@ pure */ static int add(int a, int b){
        return a-b;
    }

    public static void main(String args[]){
        System.out.println(add(2,3));
    }
}
