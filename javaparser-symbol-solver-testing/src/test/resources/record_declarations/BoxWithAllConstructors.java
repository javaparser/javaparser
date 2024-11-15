package box;

record BoxWithAllConstructors(String s) {
  public BoxWithAllConstructors(String s) {
    this.s = s;
  }

  public BoxWithAllConstructors(Integer i) {
    this(i.toString());
  }

}
