public class Test {

    // Return the index of the first true entry in the array x. Return -1 if all are false.

    //@requires (x.length==4);
    //@ensures (\result>=-1) && (\result<4);
    //@ensures (\result>=0)==>x[\result];
    //@ensures (\result==-1)==>(\forall int i; (0<=i) && (i<4); !x[i]);
    public static int findFirstSetLoop(boolean[] x) {
        //@loop_invariant 0<=i && i<=4;
        for (int i=0; i>=0 && i<4; i++)
            if (x[i]) return i;
        return -1;
    }

}
