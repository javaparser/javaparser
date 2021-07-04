
public class test3 {
	public final /*@ non_null readonly @*/ int [] binarr = new int[]
	{0x1,0x2,0x4,0x8,
	0x10,0x20,0x40,0x80,
	0x100,0x200,0x400,0x800,
	0x1000,0x2000,0x4000,0x8000,
	0x10000,0x20000,0x40000,0x80000,
	0x100000,0x200000,0x400000,0x800000,
	0x1000000,0x2000000,0x4000000,0x8000000,
	0x10000000,0x20000000,0x40000000
};
////@ public invariant binarr.length == 31;
////@ public invariant binarr[0] == 1;
//	//@ public invariant \forall int j; 0 <= j < binarr.length; binarr[j] > 0;
//	//@ public invariant \forall int j; 0 <= j < binarr.length-1; binarr[j]*2==binarr[j+1];
//	//@ public invariant \forall int j; 0 <= j < binarr.length-1; binarr[j] == (1<<j);
	public static void test() {
		test3 test = new test3();
		int k = 50;
	//	//@ assert test.binarr.length > 0 && test.binarr.length==31;
	//	//@ assert test.binarr[0] == 1;
	//	//@ assert test.binarr[0] == 1 && \forall int j; 0 <= j < test.binarr.length-1; test.binarr[j]*2==test.binarr[j+1];
	//	//@ assert \forall int j; 0 <= j < test.binarr.length-1; test.binarr[j] <= test.binarr[j+1];
		
		// TODO: The following two are beyond the power of the solver
		// @ assert \exists int j; 0 <= j < test.binarr.length-1; test.binarr[j] <= k < test.binarr[j+1];
		// @ assert \exists int j; 0 <= j < test.binarr.length; k/test.binarr[j]==1;
		//@ assert \exists int j; 0 <= j < test.binarr.length; k/(new test3()).binarr[j]==1;
	}
	
	//@ pure
	public test3() {}
}
