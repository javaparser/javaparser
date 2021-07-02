class Base {
  int m() {
    return 0;
  }

  public static void start(Base o) {
    int i=o.m(); 
  }
}

class SubA extends Base {
  int m() {
    return 0;
  }
}
