public class ConsFresh extends Parent {

//@ public normal_behavior
//@   ensures \fresh(x);
//@ pure
public ConsFresh() {
   super();
}

}


class Parent {

public Object x;

//@ public normal_behavior
//@   ensures \fresh(x);
//@ pure
public Parent() {
   x= new Object();
}
}
