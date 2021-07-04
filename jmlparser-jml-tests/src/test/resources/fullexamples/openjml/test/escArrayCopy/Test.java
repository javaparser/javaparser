public class Test {
	
	// Add float and double cases also, when we can discriminate logics

	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyByte(byte[] a, byte b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyInt(int[] a, int b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyBoolean(boolean[] a, boolean b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyChar(char[] a, char b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyShort(short[] a, short b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ assignable b[*];
	static public void copyLong(long[] a, long b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	//@ requires a != null && a.length == 10;
	//@ requires b != null && b.length == 30;
	//@ requires \elemtype(\typeof(a)) <: \elemtype(\typeof(b));
	//@ assignable b[*];
	static public void copyObject(Object[] a, Object b[]) {
		System.arraycopy(a, 0, b, 10, a.length);
		//@ assert (\forall int i; i <10 && i <= 20; b[i] == \old(b[i]));
		//@ assert (\forall int i; 10<=i && i <20; b[i] == a[i-10]);
	}
	
	
}