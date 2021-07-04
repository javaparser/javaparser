public class Relaxed {
	//@ requires true;
	//@ ensures pat.length == 0 ==> \result == true;
	//@ ensures a.length == 0  && pat.length == 1 ==> \result == true; 
	//@ ensures a.length == 0  && pat.length > 1 ==> \result == false; 
	//@ ensures pat.length > 0 && a.length > 0 ==>  Relaxed.diffIndex(pat, a) == pat.length ==> \result == true;
	 public static boolean isRelaxedPrefix(int[] pat, int[] a) {
	    int shift = 0;
	    int index = 0;

	    if (pat.length == 0) return true;
	    if (a.length == 0 && pat.length == 1) return true;
	    if (a.length == 0 && pat.length > 1) return false;
	    assert a.length > 0 && pat.length > 0;
	    if (Relaxed.diffIndex(pat, a) == pat.length) return true;
	    //@ maintaining 0 <= index && index <= pat.length;
	    //@ maintaining 0 <= index - shift && index - shift <= a.length && 0 <= shift && shift <= 1;
	   //@ maintaining  Relaxed.diffIndex(pat, a) > index ==>(\forall int i; 0 <= i && i < index; pat[i] == a[i]) ;
	   //@ maintaining  Relaxed.diffIndex(pat, a) >  index ==> (\forall int j; Relaxed.diffIndex(pat, a) < j && j < index; pat[j] == a[j - 1]);
	   //@ decreases pat.length - index - shift;
	    while((pat.length > index ) && (a.length > index - shift)){
	        if (pat[index] != a[index - shift]){
	            if (shift == 0) shift = 1;
	            else return false;
	        }

	         index = index + 1;

	    }
	    if (a.length == index - shift && pat.length > index ) return false;
	    return true;
	}


	//@ requires true;
	//@ ensures 0 <= \result && \result <= pat.length; 
	//@ ensures (\forall int i; 0 <= i && i < \result; pat[i] == a[i]);
	//@ ensures (pat.length > \result) && (a.length > \result) ==> pat[\result] != a[\result];
	public /*@ pure function @*/ static int diffIndex(int[] pat, int[] a)
	{
	  int index = 0;
	  //@ maintaining 0 <= index && index <= pat.length && index <= a.length;
	  //@ maintaining (\forall int i; 0 <= i && i < index; pat[i] == a[i]);
	  //@ decreases pat.length - index;
	  while((pat.length > index) && (a.length > index))
	  {
	      if(pat[index] == a[index]){
	        index = index + 1;
	      } else {
	        return index;
	      }

	  }
	  return index;
	}
}