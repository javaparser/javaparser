@org.jmlspecs.annotation.NullableByDefault
public class TestInteger {

	@org.jmlspecs.annotation.SkipEsc
	public static void main(String... args) {
		esc(10,42,-7);
	}
	
	@org.jmlspecs.annotation.CodeJavaMath
	public static void esc(int i, int j, /*@ non_null */ Integer z) {
		Integer a = new Integer(i);
		Integer c = new Integer(i+1);
		Integer b = i;
		//@ assert a != null;
		//@ assert b != null;
		// @ assert a != b; // Does not necessarily hold
		//@ assert a.intValue() == b.intValue();
		//@ assert a.equals(b);
		//@ assert a.intValue() != c.intValue();
		//@ assert !a.equals(c);
		//@ assert ((int)a) == i;
		int k = b;
		//@ assert k == i;
		//@ assert a.equals(b);
		//@ assert !a.equals(c);
		//@ assert !a.equals(null);
		//@ assert Integer.MIN_VALUE == -2147483648;
		//@ assert Integer.MAX_VALUE == 2147483647;
        //@ assert Integer.BYTES == 4;
        //@ assert Integer.SIZE == 32;
        //@ assert Integer.TYPE == int.class;
		
        //@ assert \typeof(a) == \type(Integer);
        //@ assert \typeof(a) <: \type(Number);
		//@ assert \typeof(a) != \type(Object);
		
		int s = i+j;
        //@ assert Integer.sum(i,j) == s;
        //@ assert Integer.max(i,j) == (i>j ? i : j);
        //@ assert Integer.min(i,j) == (i<j ? i : j);
        //-RAC@ assert z.intValue() == z.theInteger;
		byte by = (byte)z.intValue();
        //@ assert z.byteValue() == by;
		long lg = (long)z.intValue();
        //@ assert z.longValue() == lg;
		short sh = (short)z.intValue();
        //@ assert z.shortValue() == sh;
        //@ assert Integer.signum(i) == (i > 0 ? 1 : i == 0 ? 0 : -1);
		
		//@ assert z.hashCode() == z.intValue();
		//@ assert Integer.hashCode(j) == j;
		// TODO - divideUnsigned, doubleValue, floatValue, remainderUnsigned
		
		// FIXME - compare operations
		// compare, compareTo, compareUnsigned
		
		// FIXME _ bit operations
		// bitCount, highestOneBit, lowestOneBits, numberOfLeadingZeros, numberOfTrailiongZeros
		// reverse, reverseBytes, rotateLeft, rotateRight
		
        // TODO: describeConstable, getInteger, resolveConstantDesc
		// TODO: clone, getClass

		// FIXME - string operations
		// decode, parseInt, parseUnsignedInt, valueOf
		// toBionaryString, toHexString, toOctalString, toUnsigned...
		
		
//		String s = a.toString();
//		int k = Integer.parseInt(s);
//		//@ assert k == i;
//		s = Integer.toString(a);
//		k = Integer.parseInt(s);
//		//@ assert k == i;
		
		//@ assert a.hashCode() == i;
	}
}
