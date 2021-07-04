
import org.jmlspecs.annotation.*; // FIXME - this should be able to go away
public class Test {
	
	Object f;
	
	// Using a parameter
	
	void m(Object o) {
		@NonNull Object oo = o; // Error because .jml file says o is Nullable
	}
	
	void m2(Object o) {
		Object oo = o; // Error because .jml file says o is Nullable
	}
	
	void m3(Object o) {
		@Nullable Object oo = o; // OK
	}
	
	void p() {
		@NonNull Object oo = new Object();
		oo = f; // Error because f is declared Nullable
	}
	
	void p2() {
		Object oo = new Object();
		oo = f; // Error because f is declared Nullable
	}
	
	void p3() {
		@Nullable Object oo = new Object();
		oo = f; // OK
	}
	
	// Using a return value
	
    void q() {
    	@NonNull Object oo = n(); // Error because n is declared nullable
    }
    
    // Assigning a return value
    
    Object n() { return null; }
    Object nn() { return f; } // Error because f is nullable but nn is not
    
    // Assigning a parameter
    
    void t(Object o) {
    	o = null; // Error - o is NonNull by default
    }
	
    void tt(Object ottm) {
    	ottm = null; // OK
    }
    
    // Using a local variable

	void v() {
		Object o = new Object();
		@NonNull Object oo = o; // OK - o is nonnull by default
	}
	
	// Initializing a field

	Object fi = null ; // Error - fi is nonnull by default
	Object fii = null ; // OK - fii is nullable by declaration
	@NonNull Object fiii = null ; // OK - fi is nonnull by declaration here that is ignored
	// Assigning a field
	
	void mf() {
		fi = null; // Error - fi is nonnull by default
	}
	
	void mf2() {
		fii = null;  // OK - fii is nullable
	}
	
	// Using a field
	void mf3() {
		@NonNull Object q = fi; // OK
	}
	void mf4() {
		@NonNull Object q = fii; // Error
	}
	Test() { fi = fiii = new Object(); }
}


class A { // NullableByDefault
	
    Object fnn;
    Object f;
    
    // Initializing a field

	Object fi = null ; // OK - fi is nullable by default
	Object fii = null ; // Error - fii is nonnull
	@NonNull Object fiii = null ; // OK - fiii is nullable; this declaration is ignored
	// Assigning a field

	void mf() {
		fi = null; // OK - fi is nullable by default
	}
	
	void mf2() {
		fii = null; // Error - fii is nonnull
	}
	
	// Using a field
	void mf3() {
		@NonNull Object q = fi; // Error - fi is nullable
	}
	void mf4() {
		@NonNull Object q = fii; // OK
	}

	
	
	void m() {
		Object o = null; // OK because .jml file says @NullableByDefault
	}
	
	// Assigning a return value
	
	Object mnn() {
		return f; // Error f is nullable, mnn is non null
	}
	
	// Assigning a parameter
	
    void t(Object o) {
    	o = null; // OK
    }
    void tt(Object ott) {
    	ott = null; // Error - ott is NonNull
    }
    A() { fnn = fii = fiii = new Object(); }
}
class B { // NullableByDefault
	
	// Initializing local variables, using a parameter
	
	void m(Object om) {
		@NonNull Object oo = om; // Error because .jml file says o is Nullable
	}
	
	void m2(Object om2) {
		Object oo = om2; // OK because .jml file says oo is Nullable
	}
	
	void m3(Object om3) {
		@Nullable Object oo = om3; // OK
	}
	
	void mn(Object omn) {
		@NonNull Object oo = omn; // OK because .jml file says o is NonNull
	}
	
	void mn2(Object omn2) {
		Object oo = omn2; // OK because .jml file says o is NonNull
	}
	
	void mn3(Object omn3) {
		@Nullable Object oo = omn3; // OK
	}
	
	// Using a local variable
	
	void v(Object ooo) {
		Object o = ooo;
		@NonNull Object oo = o; // Error - o is nullable by default
	}
}
