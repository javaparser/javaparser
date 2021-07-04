public class Relaxed { 
	//@ ensures pat.length > 0 && a.length > 0 ==>  Relaxed.diffIndex(pat, a) == pat.length ==> \result == true;
    public static boolean isRelaxedPrefix(int[] pat, int[] a) {
        if (Relaxed.diffIndex(pat, a) == pat.length) return true;
        //  THIS IS OK @ maintaining  (\let int k = Relaxed.diffIndex(pat, a); k >  0 ==> (\forall int j; k < j && j < 0; pat[j] == a[j - 1]));
        //@ maintaining  ( Relaxed.diffIndex(pat, a) >  0 ==> (\forall int j; Relaxed.diffIndex(pat, a) < j && j < 0; pat[j] == a[j - 1]));
        //@ loop_writes pat;
        while(pat.length > 0){}
        return true;
    }

    public static boolean isRelaxedPrefix2(int[] pat, int[] a) {
        if (Relaxed.diffIndex(pat, a) == pat.length) return true;
        //  THIS IS OK @ maintaining  (\let int k = Relaxed.diffIndex(pat, a); k >  0 ==> (\forall int j; k < j && j < 0; pat[j] == a[j - 1]));
        //@ maintaining  ( Relaxed.diffIndex(pat, a) >  0 ==> (\forall int j; Relaxed.diffIndex(pat, a) < j && j < 0; pat[j] == a[j - 1]));
        while(pat.length > 0){}
        return true;
    }

	public /*@ pure  @*/ static int diffIndex(int[] pat, int[] a)
	{
		return 0;
	}
}
