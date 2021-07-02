abstract class AbstractCollection {
}

interface List {
}

abstract class AbstractList 
  extends AbstractCollection implements List {
}

class ArrayList extends AbstractList {

  static ArrayList sal;
  static int v;
  static short j;

  Object[] data;
  int length;

  public static void demo1() {
    int i=0;
  }

  public static void demo2(ArrayList para1) {
    if (para1==null)
      j=0;
    else
      j=1;
    para1.demo3();
  }

  void demo3() {
    this.length=this.length+1;
  }

  int inc(int arg) {
    return arg+1;
  }

}
