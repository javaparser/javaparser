//@ non_null_by_default
public class Test {
	
	public void foo(Class<?> clazz) {
		
	}
	
	public void m() {
		foo(Object.class);
	}	
	public void mm() {
		Object o = Integer.class;
	}
}
