
public class test1 {
	public static final /*@ non_null readonly static_initializer @*/ int [] binarr = new int[]
	{0x1,0x2,0x4,0x8,
	0x10,0x20,0x40,0x80,
	0x100,0x200,0x400,0x800,
	0x1000,0x2000,0x4000,0x8000,
	0x10000,0x20000,0x40000,0x80000,
	0x100000,0x200000,0x400000,0x800000,
	0x1000000,0x2000000,0x4000000,0x8000000,
	0x10000000,0x20000000,0x40000000
};
//@ public static invariant binarr.length > 0 && binarr.length==31;
//@ public invariant binarr[0]==1 && \forall int j;0 <= j < binarr.length-2;binarr[j]==binarr[j+1]/2;
//@ public invariant \forall int j;0 <= j < binarr.length-1;binarr[j] <= binarr[j+1];
}
