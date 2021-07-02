class Base {
  static int i;

  int m() {
    return 0;
  }

  public static void start(Base o) {
    i=o.m(); 
  }
}

class SubA extends Base {
  int m() {
    return 0;
  }
}

