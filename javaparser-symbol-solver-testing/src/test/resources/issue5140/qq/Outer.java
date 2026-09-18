package qq;

public class Outer {

    public Object viaObjectCreation() {
        return new Mid.Nested();
    }

    public void viaTypeUse() {
        Mid.Nested n = null;
    }

    public Object viaOrdinaryImport() {
        return new Mid.Other();
    }

    public Object nestedTypeOfTheTypeItself() {
        return new Sink.Nested();
    }

    public Object nestedTypeInheritedFromAnAncestor() {
        return new Derived.Inherited();
    }
}
