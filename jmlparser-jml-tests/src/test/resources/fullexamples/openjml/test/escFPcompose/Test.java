import java.util.function.Function;

public class Test {
	
    //@ public normal_behavior
	//@   requires f != null && g != null;
	//@   ensures \result != null && (\forall Integer i,r;; \ensures(\result,r,i) == (\exists Integer t;; \ensures(g,t,i) && \ensures(f,r,t)));
	public static Function<Integer,Integer> compose(Function<Integer,Integer> f, Function<Integer,Integer> g) {
		return i -> f.apply(g.apply(i));
	}
	
	public static class Dec implements Function<Integer,Integer> {
		//@ also public normal_behavior
		//@   requires i != Integer.MIN_VALUE;
		//@   ensures \result != null && \result == i - 1;
		public Integer apply(Integer i) {
			return i-1;
		}
	}
	
	public Function<Integer,Integer> dec = i -> i-1;
	
	public static class Inc implements Function<Integer,Integer>  {
		//@ also public normal_behavior
		//@   requires i != Integer.MAX_VALUE;
		//@   ensures \result != null && \result == i + 1;
		public Integer apply(Integer i) {
			return i+1;
		}
	}
	
	public Function<Integer,Integer> inc = i -> i-1;
	
	public static class Bump implements Function<Integer,Integer>  {
		//@ also public normal_behavior
		//@   requires i != Integer.MAX_VALUE;
		//@   ensures \result != null && \result > i;
		public Integer apply(Integer i) {
			return i+1;
		}
	}
	
	public Function<Integer,Integer> bump = i -> i-1;
	
	
	//@   requires k != null && k != Integer.MAX_VALUE;
	public void m(Integer k) {
		Integer h = compose(new Dec(),new Inc()).apply(k);
		//@ assert (int)h == (int)k;
	}
	
//	//@   requires k != Integer.MAX_VALUE;
//	public void mm(int k) {
//		Integer h = compose(Dec,Bump).apply(k);
//		//@ assert h >= k;
//	}
//	
//	//@   requires k != Integer.MAX_VALUE;
//	public void mmbad(int k) {
//		Integer h = compose(Dec,Bump).apply(k);
//		//@ assert h == k;
//	}
}