@org.jmlspecs.annotation.SpecBigintMath
@org.jmlspecs.annotation.CodeJavaMath
class Big {
    //@requires  i *  j *  k <  Integer.MAX_VALUE;
    static int safe_mult(int i, int j, int k) {
	return i * j * k;
    }

    public static void main(String[] args) {
	System.out.println("Hello, world");
	System.out.println(safe_mult(1, 5, 6));
	System.out.println(safe_mult(1000000, 6, 8));
	System.out.println(safe_mult(1000000, 1000, 1000));
    }
}
