package tests;

public class ModelClassExampleBugSub2<E> extends ModelClassExampleBug<E> {
    
   /*@ public model class MIndexedContents extends ModelClassExampleBug<E>.MContents {
          public boolean foo() { return false; }
        }
        
        public static model class SMIndexedContents extends ModelClassExampleBug<E>.SMContents { // ERROR
          public boolean foo() { return false; }
        }
    @*/

    public class IndexedContents extends ModelClassExampleBug<E>.Contents {
        public boolean foo() { return false; }
      }
    
    protected ModelClassExampleBugSub2() {}

}
