package tests;

public class ModelClassExampleBug<E> {
    
    /*@ public model class MContents {
    public boolean foo() { return true; }
    }
    @*/

    /*@ public static model class SMContents {
    public boolean foo() { return true; }
    }
    @*/

    public class Contents {
        public boolean foo() { return true; }
    }

    public static class SContents {
        public boolean foo() { return true; }
    }


    protected ModelClassExampleBug() {}
}