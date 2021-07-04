public class Test {
	
	/*@
   	@   requires array != null;
   	@   assignable \nothing;
   	@   ensures ( 0 <= \result
   	@   		&& \result < array.length
   	@   		&& array[\result] == 5)
   	@   		|| \result == array.length ;
   	@   ensures (\forall int j; 0 <= j && j < \result; array[j] != 5);
   	@*/
	public static /*@pure@*/ int findFirstFivewithLogicalOp(int[] array) {
		int k = 0;
		
		/*@ loop_invariant
   		@   0 <= k && k <= array.length 
   		@   && (\forall int i; 0 <= i && i < k; array[i] != 5);
   		@  decreases array.length - k;
   		@*/
		for (; k < array.length; k++) {
			if (array[k] == 5) {
				break;
			}
		}
		return k;
	}
	
	/*@
   	@   requires array != null;
   	@   assignable \nothing;
   	@   ensures \result == array.length || ( 0 <= \result
   	@   		&& \result < array.length
   	@   		&& array[\result] == 5)
   	@   		  ;
   	@   ensures (\forall int j; 0 <= j && j < \result; array[j] != 5);
   	@*/
	public static /*@pure@*/ int findFirstFivewithLogicalOpB(int[] array) {
		int k = 0;
		
		/*@ loop_invariant
   		@   0 <= k && k <= array.length 
   		@   && (\forall int i; 0 <= i && i < k; array[i] != 5);
   		@  decreases array.length - k;
   		@*/
		for (; k < array.length; k++) {
			if (array[k] == 5) {
				break;
			}
		}
		return k;
	}
	
	/*@
   	@   requires array != null;
   	@   assignable \nothing;
   	@   ensures ( 0 <= \result
   	@   		&& \result < array.length
   	@   		&& array[\result] == 5)
   	@   		| \result == array.length ;
   	@   ensures (\forall int j; 0 <= j && j < \result; array[j] != 5);
   	@*/
	public static /*@pure@*/ int findFirstFiveWithBitOp(int[] array) {
		int k = 0;
		
		/*@ loop_invariant
   		@   0 <= k && k <= array.length 
   		@   && (\forall int i; 0 <= i && i < k; array[i] != 5);
   		@  decreases array.length - k;
   		@*/
		for (; k < array.length; k++) {
			if (array[k] == 5) {
				break;
			}
		}
		return k;
	}
	
}