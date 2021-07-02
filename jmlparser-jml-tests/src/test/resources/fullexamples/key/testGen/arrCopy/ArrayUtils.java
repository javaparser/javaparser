public class ArrayUtils {
   /*@ 
     public normal_behaviour 
     ensures (\forall int i; 0<=i && i<a.length; a[i]==b[i]);
   @*/
 public void arrCopy(int[] a, int[] b){
	 for(int i=0; i<a.length; i++){
	      b[i]=a[i];	      
	 }
 }
}