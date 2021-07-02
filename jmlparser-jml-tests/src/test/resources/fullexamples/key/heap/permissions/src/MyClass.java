public class MyClass {

  public int a;
  public int b;
  public Object o;
  public /*@ nullable @*/ int[] array;

  /*@ public normal_behavior
        requires<permissions> \dl_writePermission(\permission(this.o));
        ensures<permissions>  \permission(this.o) == \old(\permission(this.o));
        ensures this.o != \old(this.o);
        ensures \fresh(this.o);
        assignable<heap> this.o;
        assignable<permissions> this.o; @*/
  public void method0() {
    o = new Object();
  }

  /*@ public normal_behavior
        requires<permissions> \dl_writePermission(\permission(this.o));
        ensures \fresh(this.o);
        assignable<heap> this.o;
        assignable<permissions> \nothing; @*/
  public void method1() {
    o = new Object();
  }

  /*@ public normal_behavior
        requires<permissions> \dl_writePermission(\permission(this.a));
        requires<permissions> \dl_readPermission(\permission(this.b));
        ensures this.a == this.b;
        assignable this.a;
        assignable<permissions> \nothing; @*/
  public void setAB() {
    this.a = this.b; // Needs permissions
    MyClass tmp = new MyClass();
    tmp.a = 1; // Permissions OK - new object
    tmp.b = 1;
  }

  /*@ public normal_behavior
        requires array != null;
        requires<permissions> \dl_readPermission(\permission(this.array));
        requires<permissions> (\forall int i; i>=0 && i<array.length;
            \dl_writePermission(\permission(this.array[i])));
        ensures (\forall int i; i>=0 && i<array.length; this.array[i] == 0);
        assignable<heap> array[*];
        assignable<permissions> \strictly_nothing;
    @*/
  public void method3() {
    /*@ loop_invariant i>=0 && i<=array.length;
        loop_invariant (\forall int j; j>=0 && j<array.length;
              j < i ? this.array[j] == 0 : this.array[j] == \old(this.array[j]));
        assignable<heap> array[*];
        assignable<permissions> \strictly_nothing;
        decreases array.length - i; @*/
    for(int i=0; i<array.length; i++) {
      array[i] = 0;
    }
  }
}
