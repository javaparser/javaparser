module com.github.javaparser.testmodule {
  exports com.github.javaparser.testpackage;
  exports com.github.javaparser.testpackage2 to java.base, java.logging;
  exports com.github.javaparser.testpackage3;
  opens com.github.javaparser.testpackage;
}
