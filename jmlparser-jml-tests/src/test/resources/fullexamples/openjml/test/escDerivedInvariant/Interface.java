public interface Interface {

//@ public invariant good();

//@ pure helper
boolean good();

}

class Derived implements Interface {

//@ also ensures \result;
//@ pure helper
public boolean good() {
   return true;
}

public Derived() {}

}


