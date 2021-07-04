public class Prime {

//@ public normal_behavior
//@  requires n > 0;
public static /*@ pure helper @*/ boolean is_prime(int n) {
    int maxInt = ((Double) Math.floor(Math.sqrt(n))).intValue();
    //@ assume maxInt >= 0 && maxInt * maxInt <= n && n < (maxInt+1)*(maxInt+1);
    //@ loop_invariant 1 <= i && i <= maxInt + 1;
    //@ loop_invariant (\forall int j; 1 <= j && j < i; (n%j) != 0);
    //@ loop_decreases maxInt + 1 - i;
    for (int i = 1; i <= maxInt; i++) {
        if ((n%i)==0) {
            //@  assert !(\forall int j; 1 <= j <= maxInt; (n%j) != 0);
            return false;
        }
    }
    //@  assert (\forall int j; 1 <= j <= maxInt; (n%j) != 0);
    return true;
}
}