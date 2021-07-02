public class PositiveArrayElements{

    /*@ public normal_behavior
      @  ensures \result.length==(\num_of int j; 0<=j && j<t.length; t[j]>0);
      @  ensures (\forall int i; 0<=i && i<t.length && t[i]>0; 
      @   (\exists int j; 0<=j && j<\result.length; \result[j]==t[i]));
      @  ensures (\forall int i; 0<=i && i<\result.length; 
      @   (\exists int j; 0<=j && j<t.length; \result[i]==t[j]));
      @*/
    int[] m(int[] t) {
	int i, count = 0;
	/*@ loop_invariant count==(\num_of int j; 0<=j && j<i; t[j]>0) && 
	  @   i<=t.length; 
	  @ decreasing t.length-i;
	  @ assignable i, count;
	  @*/
	for (i=0; i < t.length; i++)
	    if (t[i] > 0) count++;
	int[] u = new int[count];
	count = 0;
	/*@ loop_invariant (\forall int k; 0<=k && k<i && t[k]>0; 
	  @   (\exists int j; 0<=j && j<count; u[j]==t[k])) &&
	  @   (\forall int k; 0<=k && k<count; 
	  @   (\exists int j; 0<=j && j<i; u[k]==t[j])) &&
	  @     count==(\num_of int j; 0<=j && j<i; t[j]>0);
	  @ decreasing t.length-i;
	  @ assignable i, count, u[*];
	  @*/	
	for (i=0; i < t.length; i++)
	    if (t[i] > 0) u[count++]= t[i];
	return u;
    }

}
