public class StackOverflowTestCase {
	private C c = new C();

	public void method1() {
		String localVariable = ConstantA.b.new innerClassInB(null, null).toString();
		System.out.println(localVariable);
	}
}