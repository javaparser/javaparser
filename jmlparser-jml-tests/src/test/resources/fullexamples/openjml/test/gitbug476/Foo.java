public class Foo {

	public static final int TEN = 10;
	//@static invariant TEN == 10;

	public static void bar(){
		//@assert TEN > 0;
	}

	public static class In {
		public static void foo(){
			//@ assert TEN > 0;
		}
	}

}