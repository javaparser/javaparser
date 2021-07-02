class MyClient {
    
    MyClass mc;
    int i;
    //@ invariant mc.\inv && \disjoint(this.*, mc.footprint);
    
    
    //@ assignable \nothing;
    MyClient() {
	mc = new MyClass();
    }
    
    //@ assignable i;
    void invariantPreservation() {
	i++;
    }
    
    
    //@ assignable mc, i;
    void dependencyContracts() {
	mc = new MyClass();
	i++;
	new Object();
    }

    
    /*@ assignable i, mc.footprint;
      @ ensures \result == 388;
      @*/
    int operationContracts() {
	i = 360;
	i = mc.add27(++i);
	return i;
    }
}
