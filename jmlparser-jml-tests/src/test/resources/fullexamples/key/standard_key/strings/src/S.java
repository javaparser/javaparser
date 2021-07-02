public final class S {

    public final static String ONE = "ONE";
    public final static String TWO = "TWO";
    public final static String COMPILE_TIME_CONSTANT = "CTC" + 1/2;
    public final static String NO_COMPILE_TIME_CONSTANT = "NCTC" + 1/0;

    public static void start () {
	String cpOne = new String(ONE);
	String cpTwo = new String(TWO);
	String cpThree = new String("THREE");

	if (check(ONE, ONE) != 0) {
	    throw new RuntimeException();
	}
	if (check(ONE, TWO) != -1) {
	    throw new RuntimeException();
	}
	if (check(ONE, cpOne) != 1) {
	    throw new RuntimeException();
	}	
    }


    public static int check(String fst, String snd) {

        if (fst == snd) {
	    return 0;
	}

	if (fst.equals(snd)) {
	    return 1;
	}

	return -1;
    }


    public String toString() {
	return "KeY";
    }
}
