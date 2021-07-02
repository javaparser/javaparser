class SITA3{
     public int[] a1;
     public int[] a2;
     int i, j;


 /*@ public normal_behaviour
   @   requires 0 <= l && l < r && 
   @    r <= a1.length && r <= a2.length;
   @   assignable \nothing;
   @   ensures ( l <= \result && \result < r && 
   @   a1[\result] ==  a2[\result])
   @   | \result == r ;
   @   ensures (\forall int j; l <= j && j < \result;
   @    a1[j] !=  a2[j] );
   @*/
 public int  commonEntry(int l, int r) {
   int k = l;
       
 /*@ loop_invariant
   @   l <= k && k <= r 
   @   && (\forall int i; l <= i && i < k; a1[i] != a2[i] );
   @
   @  assignable \nothing;
   @  decreases a1.length - k;
   @*/
   while(k < r) {
      if(a1[k] == a2[k]){break;}
       k++;     }
    return k;
    }


   /*@ public normal_behaviour
     @  requires  0<= pos1 && 0<= pos2 &&
     @  pos1 < a.length && pos2 < a.length ;  
     @  ensures  
     @    a[pos1]  == \old(a[pos2]) &&
     @    a[pos2]  == \old(a[pos1]);
     @  assignable a[pos1], a[pos2];
     @*/
 
    public void  swap(int[] a,int pos1, int pos2) {
	int temp;
        temp = a[pos1]; a[pos1] = a[pos2] ; a[pos2] = temp;
    }

 /*@ public normal_behaviour
     @  requires  a1.length == a2.length;
     @  ensures  (\forall int i;0<= i && i < a1.length; 
     @      a1[i] == a2[i] ==> 
     @    (\forall int j;0<= j && j < i; a1[j] == a2[j]));
     @  assignable a1[*],a2[*];
     @*/

    public void  rearrange(){
      int m = 0 ;
      int k = 0;

   /*@ maintaining
     @ 0 <= m && m <= a1.length && k <= m && 0 <= k &&
     @ (\forall int i;0<= i && i < k; 
     @      a1[i] == a2[i]) && 
     @  (\forall int j; k <= j && j < m; 
     @    a1[j] != a2[j]) ;
     @ 
     @  assignable a1[*],a2[*];
     @  decreases a1.length - m;
     @*/
    while (m < a1.length) {
	  m = commonEntry(m,a1.length);
	  if (m < a1.length)       {
	      swap(a1,m,k);
	      if (a1 != a2) { swap(a2,m,k);}
	      k = k+1 ; m = m+1;}}

}
}
