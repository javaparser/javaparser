public class Opt {

//@ public normal_behavior
//@   requires i >= 42;
//@   ensures \result == 420;
public int n(int i) { return 420; }

public int m(int i) {

   return n(i);

}
}
