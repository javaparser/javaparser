public class Examples{

    /*@ public normal_behavior
      @  requires (\forall int i,j; 0<=i && i<j && j<f.length; f[i]<f[j]);
      @  requires (\forall int i,j; 0<=i && i<j && j<g.length; g[i]<g[j]);
      @  requires f!=null && g!=null;
      @  ensures \result==(\bsum int i; 0; f.length;
      @            (\bsum int j; 0; g.length; (f[i]==g[j]?1:0)));
      @*/
    public static int coincidenceCount1(int[] f, int[] g){
	int ct=0, m=0, n=0;
	/*@ loop_invariant m>=0 && n>=0 && m<=f.length && n<=g.length &&
	  @    ct ==(\bsum int i; 0; m;
	  @            (\bsum int j; 0; n; (f[i]==g[j]?1:0))) &&
	  @    (m==f.length || (\forall int j; j>=0 && j<n; g[j]<f[m])) &&
	  @    (n==g.length || (\forall int i; i>=0 && i<m; f[i]<g[n]));
	  @ assignable ct, n, m;
	  @ decreasing f.length-m + g.length-n;
	  @*/
	while(m<f.length && n<g.length){
	    if(f[m]<g[n]){
		m++;
	    }else if(g[n]<f[m]){
		n++;
	    }else{
		ct++;
		m++;
		n++;
	    }
	}
	return ct;
    }

    /*@ public normal_behavior
      @  requires a!=null;
      @  ensures \result==(\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum0(int[] a)
    {
	int s = 0;
	int n = 0;
	/*@ loop_invariant s ==(\bsum int i; 0; n; a[i]);
	  @ assignable s, n;
	  @ decreasing a.length-n;
	  @*/
	while(n < a.length)
	{
	    s += a[n];
	    n++;
	}
	return s;
    }

    /*@ public normal_behavior
      @  requires a!=null;
      @  ensures \result==(\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum1(int[] a)
    {
	int s = 0, n=0;
	/*@ loop_invariant s + (\bsum int i; n; a.length; a[i])==(\bsum int i; 0; a.length; a[i]);
	  @ assignable s, n;
	  @ decreasing a.length-n;
	  @*/
	while(n < a.length)
	{
	    s += a[n];
	    n++;
	}
	return s;
    }

    /*@ public normal_behavior
      @  requires a!=null;
      @  ensures \result==(\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum2(int[] a)
    {
	int s = 0, n = a.length;
	/*@ loop_invariant s==(\bsum int i; n; a.length; a[i]);
	  @ assignable s, n;
	  @ decreasing n;
	  @*/
	while(n > 0)
	{
	    s += a[--n];
	}
	return s;
    }

    /*@ public normal_behavior
      @  requires a!=null;
      @  ensures \result==(\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum3(int[] a)
    {
	int s = 0, n = a.length;
	/*@ loop_invariant s + (\bsum int i; 0; n; a[i])==(\bsum int i; 0; a.length; a[i]);
	  @ assignable s, n;
	  @ decreasing n;
	  @*/
	while(n > 0)
	{
	    s += a[--n];
	}
	return s;
    }

}
