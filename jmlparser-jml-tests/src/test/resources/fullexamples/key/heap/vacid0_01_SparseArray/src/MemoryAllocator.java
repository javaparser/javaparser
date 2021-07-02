public class MemoryAllocator {
    
    /*@ normal_behaviour
      @   requires 0 <= size;
      @   ensures \fresh(\result);      
      @   ensures \result.length == size;
      @*/
    public static /*@pure@*/ int[] alloc(int size) {
	int[] result = new int[size];
	/*@ loop_invariant 0 <= i && i <= size;
	  @ assignable result[*];
	  @ decreases size - i;	  
	  @*/
	for(int i = 0; i < size; i++) {
	    result[i] = -359;
	}
	return result;
    }
    
    
    /*@ normal_behaviour
      @   requires 0 <= size;
      @   ensures \fresh(\result);    
      @   ensures \result.length == size;
      @   ensures (\forall int x; 0 <= x && x < size; 0 <= \result[x]);
      @*/
    public static /*@pure@*/ int[] alloc_unsigned(int size) {
	int[] result = new int[size];
	/*@ loop_invariant 0 <= i && i <= size && (\forall int x; 0 <= x && x < i; 0 <= result[x]);
	  @ assignable result[*];
	  @ decreases size - i;
	  @*/	
	for(int i = 0; i < size; i++) {
	    result[i] = 1234;
	}
	return result;
    }
}
