public class ReverseArray {

    /*@ public normal_behavior
          requires 0 <= s.length && s.length < Integer.MAX_VALUE;
          ensures \fresh(\result);
          ensures (\forall int i; 0 <= i < s.length;
                     \result[i] == s[s.length - 1 - i]);
      @*/
    public /*@ pure @*/ char[] reverse(char[] s) {
        final int len = s.length;
        //@ assert len == s.length;
        char[] res = (char[]) new char[len];
        //@ assert len == res.length;
        int i = len-1;
        /** rlen tells how many elements of res are defined. **/
        int rlen = 0;
        //@ maintaining len == res.length;
        //@ maintaining -1 <= i < len;
        //@ maintaining rlen == (len-1) - i && rlen <= len;
        /*@ maintaining (\forall int j; 0 <= j < len-1-i;
                                 res[j] == s[len-1-j]); @*/
        while (0 <= i && i < len) {
            //@ assert 0 <= i < s.length && 0 <= len-i <= len;
            // System.out.println("i is " + i + ", len-1-i is " + (len-1-i));
            //@ assert res.length == len;
            //@ assert (len-1-i)+1 <= len;
            res[len-1-i] = s[i];
            //@ assert res[(len-1-i)] == s[i];
            rlen += 1;
            //@ assert rlen == ((len-1) - i) + 1;
            // System.out.println("res[len-1-i] == s[i] is " + (res[len-1-i] == s[i]));
            i--;
        }
        //@ assert i == -1;
        //@ assert rlen == len;
        /*@ assert (\forall int k; 0 <= k < len; res[k] == s[len-1 - k]); @*/
        return res;
    }

    public static void main(String [] argv) {
        ReverseArray ra = new ReverseArray();
        char [] abc = new char[3];
        abc[0] = 'a'; abc[1] = 'b'; abc[2] = 'c';
        char[] revd = ra.reverse(abc);
        System.out.println("reverse(abc) is \""
                           + ReverseArray.arr2str(revd)
                           + "\"");
    }

    /*@ public normal_behavior
          ensures \result.length() == a.length;
          ensures (\forall int i; 0 <= i && i < a.length; 
                                  \result.charAt(i) == a[i]);
      @*/
    public /*@ pure @*/ static String arr2str(char[] a) {
        String res = "";
        //@ maintaining res.length() <= a.length;
        //@ maintaining res.length() == \count;
        //@ maintaining (\forall int j; 0 <= j < res.length(); res.charAt(j) == a[j]);
        for (char c : a) {
            res += c;
        }
        return res;
    }
}
