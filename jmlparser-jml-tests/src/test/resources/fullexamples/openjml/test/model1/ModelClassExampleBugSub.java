package tests;

public class ModelClassExampleBugSub<E> extends ModelClassExampleBug<E> {
    
    public class IndexedContents extends ModelClassExampleBug<E>.Contents {
        public boolean foo() { return false; }
      }
    
    public static class SIndexedContents extends ModelClassExampleBug<E>.SContents { // ERROR
        public boolean foo() { return false; }
      }
    
    protected ModelClassExampleBugSub() {}

}
