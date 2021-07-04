import java.lang.Math;
public class CopySign {
	public static void copySign_test1() {
		double a = Math.copySign(64.0, -128.0);
		//@ assert a == -64.0;
	}
	public static void copySign_test2() {
		//@ assume !Double.isNaN(-64.0);
		double a = Math.copySign(-64.0, -128.0);
		//@ assert a == -64.0;
	}
	public static void copySign_test3() {
		double a = Math.copySign(64.0, 128.0);
		//@ assert a == 64.0;
	}
	public static void copySign_test4() {
		//@ assume !Double.isNaN(-64.0);
		double a = Math.copySign(-64.0, 128.0);
		//@ assert a == 64.0;
	}
	public static void copySign_testA1(double i, double j) {
		double a = Math.copySign(i,j);
		//@ assert 0 < i && 0 < j ==> a == i;
		//@ assert 0 < i && 0 > j ==> a == -i;
		//@ assert 0 > i && 0 < j ==> a == -i;
		//@ assert 0 > i && 0 > j ==> a == i;
	}
}