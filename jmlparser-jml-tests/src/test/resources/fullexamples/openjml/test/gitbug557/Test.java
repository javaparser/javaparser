//@ non_null_by_default
public class Test {
	
	static public class Help {
		public int nnn;
	}
	
	public Help ff = new Help();
	
	public class Inner {
		public int gg;
		
		//@ requires ff != null;   // FIXME - sxhouldn't this be nonnull be default?
		//@ requires ff.nnn == 29;
		//@ ensures gg == ff.nnn;
		//@ pure
		public Inner() {
			gg = ff.nnn;
			//@ assert ff.nnn == 29;
			//@ assert ff == Test.this.ff;
		}
	}
	
	//@ requires ff.nnn == 29;
	public void m() {
		Inner a = new Inner(); 
							// ff.nnn in precondition wrongly translated
							// also, not clear translating states that a.ff is the same as ff
	}	
}
