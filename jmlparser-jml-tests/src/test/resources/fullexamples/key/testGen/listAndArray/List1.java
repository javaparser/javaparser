/*This is a test generation example for the KeYToolPaper2014. Both methods (get and l2a) do not satisfy the specifications. 
Author: Christoph Gladisch
*/

class List1 {
/*@ nullable */ public List1 nxt;
 
/*@ public normal_behaviour
 ensures (i==0 ==> \result==this) &&
 (nxt==null || i<0 ==> \result==null) &&
 (nxt!=null && i>0 ==> \result==nxt.get(i-1));*/ 
public /*@ pure nullable */ List1 get(int i){
 if(i==0) return this;
 return (nxt==null || i<0)? null:nxt.get(i-1);
}

/*@ public normal_behaviour
requires a.length>0 && l!=null;
ensures (\forall int i;1<=i && i<a.length; 
                        a[i] == l.get(i)); */ 
public void l2a(/*@nullable */List1 l, List1[] a){            
   for(int i = 0; i< a.length; i++){
      a[i]=l;
      if(l==null){ break;}; l=l.nxt;
   }
} }
