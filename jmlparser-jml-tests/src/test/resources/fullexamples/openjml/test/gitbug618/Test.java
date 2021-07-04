import java.util.Optional;

// The reported errors are using Optional<>
// They are replicated with Opt1.
// The requires aspect is being a function 
public class Test {
	
//	public void t1(/*@ non_null */ Optional<String> o) {
//		//@ assume o.isPresent();
//		//@ assert o.value != null;
//	}
//	
//	public void q1(/*@ non_null */ Optional<String> o) {
//		//@ assert o.isPresent() ==> (o.value != null);
//	}
//	
//	public void c1(/*@ non_null */ Optional<String> o) {
//		if (o.isPresent()) {
//			//@ assert (o.value != null);
//		}
//	}
//	
//	public void r1(/*@ non_null */ Optional<String> o) {
//		//@ assume (o.value != null);
//		//@ assert o.isPresent();
//	}
	
}

 class Test2 {
	
	public void t1(/*@ non_null */ Opt1 o) {
		//@ assume o.nn();
		//@ assert o.value != null;
	}
	
//	public void q1(/*@ non_null */ Opt1 o) {
//		//@ assert o.nn() ==> (o.value != null);
//	}
	
	public void c1(/*@ non_null */ Opt1 o) {
		if (o.nn()) {
			//@ assert (o.value != null);
		}
	}
	
//	public void r1(/*@ non_null */ Opt1 o) {
//		//@ assume (o.value != null);
//		//@ assert o.nn();
//	}
//	
//	public void t2(/*@ non_null */ Opt2 o) {
//		//@ assume o.nn();
//		//@ assert o.value != null;
//	}
//	
//	public void q2(/*@ non_null */ Opt2 o) {
//		//@ assert o.nn() ==> (o.value != null);
//	}
//	
//	public void c2(/*@ non_null */ Opt2 o) {
//		if (o.nn()) {
//			//@ assert (o.value != null);
//		}
//	}
//	
//	public void r2(/*@ non_null */ Opt2 o) {
//		//@ assume (o.value != null);
//		//@ assert o.nn();
//	}
//	
//	public void t3(/*@ non_null */ Opt3 o) {
//		//@ assume o.nn();
//		//@ assert o.value != null;
//	}
//	
//	public void q3(/*@ non_null */ Opt3 o) {
//		//@ assert o.nn() ==> (o.value != null);
//	}
//	
//	public void c3(/*@ non_null */ Opt3 o) {
//		if (o.nn()) {
//			//@ assert (o.value != null);
//		}
//	}
//	
//	public void r3(/*@ non_null */ Opt3 o) {
//		//@ assume (o.value != null);
//		//@ assert o.nn();
//	}
//	
	
	
}

