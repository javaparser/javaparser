package foo;

public class C {
	public static A getFoo() {
		return new B() {
			@Override
			public void overrideMe(FindMeIfYouCan v) {
			}
		};
	}
}