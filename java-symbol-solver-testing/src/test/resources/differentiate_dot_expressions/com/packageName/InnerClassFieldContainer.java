public class InnerClassFieldContainer {
    FieldContainer outerField = new FieldContainer();
    class InnerClass {
        FieldContainer innerField = new FieldContainer();
        class InnerInnerClass {
            FieldContainer innerInnerField = new FieldContainer();
            class InnerInnerInnerClass {
                FieldContainer innerInnerInnerField = new FieldContainer();
            }
        }
    }
}

class FieldContainer {
    FieldContainer containerField = new FieldContainer();
    public String firstContainerMethod() {
        return "firstContainerMethod()";
    }
    public String secondContainerMethod() {
        return "secondContainerMethod()";
    }
    public String thirdContainerMethod() {
        return "thirdContainerMethod()";
    }
}
