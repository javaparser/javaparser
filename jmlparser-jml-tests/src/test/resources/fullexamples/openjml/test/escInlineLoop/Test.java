import java.util.stream.Stream;
public class Test {
	
	static public int ii;
	static public int[] arr = new int[5];
	
	//@ public normal_behavior
	//@ requires ii >= 0 && ii < arr.length;
	//@ old int oldI = ii;
	//@ assignable ii, arr[ii];
	//@ ensures arr[oldI] == v;
	//@ ensures ii == oldI + 1;
	static public void putAtI(int v) {
		arr[ii] = v;
		ii++;
	}
	
	public void mm() {
		
		Stream<Integer> st = Stream.<Integer>of(1,2,3,4,5);
		//@ assert st.count() == 5;
		//@ assume arr.length == 5;
		
		ii = 0;
		//@ loop_invariant Test.ii == \count;
		//@ loop_invariant (\forall int j; j>=0 && j<\count; arr[j] == j+1);
		//@ loop_modifies Test.ii, Test.arr[*];
		//@ inlined_loop;
		st.forEachOrdered(v -> putAtI(v));
		//@ assert Test.ii == st.count();
		
		//@ assert arr[0] == 1;
		//@ assert arr[4] == 5;
		//@ assert (\forall int j; j>=0 && j<arr.length; arr[j] == j+1);
	}
}

 class TestA {
	
	public int ii;
	
	//@ requires ii >= 0 && ii < arr.length;
	//@ old int oldI = ii;
	//@ assignable ii, arr[ii];
	//@ ensures arr[oldI] == v;
	//@ ensures ii == oldI + 1;
	public void putAtI(int[] arr, int v) {
		arr[ii] = v;
		ii++;
	}
	public void m() {
		
		Stream<Integer> st = Stream.<Integer>of(1,2,3,4,5);
		int[] arr = new int[5];
		//@ assert st.count() == 5;
		
		ii = 0;
		//@ loop_invariant ii == \count;
		//@ loop_invariant (\forall int j; j>=0 && j<\count; arr[j] == j+1);
		//@ loop_modifies ii, arr[*];
		//@ inlined_loop;
		st.forEachOrdered(v -> putAtI(arr,v));

		//@ show ii, st.values.length, st.count(); 
		//@ assert ii == st.count();
		
		//@ assert arr[0] == 1;
		//@ assert arr[4] == 5;
		//@ assert (\forall int j; j>=0 && j<arr.length; arr[j] == j+1);
	}
}