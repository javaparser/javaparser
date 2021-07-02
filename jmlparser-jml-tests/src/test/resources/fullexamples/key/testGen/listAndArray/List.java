/*This is a test generation example for the KeYBook 2.0. Methods L2A does not satisfy the specifications. 
Author: Christoph Gladisch
*/

final class List { 

 /*@ nullable */ public List nxt;
  
 public /*@ pure nullable */ List get(int i){
  return i==0 ? this :  
             ((nxt==null || i<0) ? null : nxt.get(i-1));
 } 
 
 /*@ public normal_behaviour
   requires a.length>0 && l!=null;
   ensures (\forall int i; 0<=i && i<a.length; a[i]==l.get(i));
 @*/ 
 public void L2A(/*@nullable */ List l, List[] a){
    for(int i=0; i<a.length; i++){
      a[i]=l;
      if(l==null) break; l=l.nxt;
    } 
 } 
}