package box;

record BoxWithNonCanonicalConstructor(String s) {
  public BoxWithNonCanonicalConstructor(Integer i) {
    this(i.toString());
  }

}
