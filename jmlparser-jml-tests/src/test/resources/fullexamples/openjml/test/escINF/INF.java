//@ non_null_by_default
public class INF {

final Object end;

public INF()  {
   this.end = mk();
}

//@ private normal_behavior
//@   ensures \fresh(\result);
//@ pure helper
private Object mk() {
   return new Object();
}

}
