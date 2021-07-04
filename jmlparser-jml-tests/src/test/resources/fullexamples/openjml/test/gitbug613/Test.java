//@ non_null_by_default
public class Test {
	
	private static int zz;
	//@ private static invariant zz == 1;
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ also public exceptional_behavior
	//@   requires i < 0;
	//@   signals_only RuntimeException;
	public Test(int i) {
		zz = 2;
		if (i < 0) throw new RuntimeException();
		zz = 1;
		aa = 3;
	}
}

class TestP {
	
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ also public exceptional_behavior
	//@   requires i < 0;
	//@   signals_only RuntimeException;
	//@ pure
	public TestP(int i) {
		aa = 1;
		if (i < 0) throw new RuntimeException();
		aa = 3;
	}
}

 class Test2 {
	
	private static int zz;
	//@ private static invariant zz == 1;
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ also public exceptional_behavior
	//@   requires i < 0;
	//@   signals_only RuntimeException;
	public Test2(int i) {
		zz = 1;
		if (i < 0) throw new RuntimeException();
		aa = 3;
	}
}
 
class Test3B {
		
		private int aa;
		//@ private invariant aa == 3;
		
		//@ public normal_behavior
		//@   requires i >= 0;
		//@ pure
		public Test3B(int i) {
			aa = 2;
		}
	}

class Test3 {
	
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ pure
	public Test3(int i) {
		aa = 3;
	}
}