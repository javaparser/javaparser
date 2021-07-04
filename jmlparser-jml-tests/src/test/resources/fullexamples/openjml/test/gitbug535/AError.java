public class AError {

//@ public behavior
//@  ensures true;
public void m() {
   throw new AssertionError();
}

//@ public normal_behavior
//@  ensures true;
public void mm() {
   throw new AssertionError();
}

//@ public behavior
//@  ensures true;
//@  signals_only Exception;
public void mmm() {
   throw new AssertionError();
}

}
