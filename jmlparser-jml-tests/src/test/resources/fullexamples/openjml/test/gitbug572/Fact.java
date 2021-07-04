// This bad syntax crashes
public class Fact {
    /*@requires n >= 0
     *@ensures \result == (\product int i; 0 < i && i <= n; i)
     */
    public static /*@ pure @*/ int fac(int n) {
        if(n<=1)
            return 1;
        else
            return n*fac(n-1);

    }
}