public class InnerClassDotExpressions {
    public static void main(String[] args) {
        InnerClassContainer.InnerClass.methodCall();
        InnerClassContainer.InnerClass.InnerInnerClass.innerMethodCall();
        InnerClassContainer.InnerClass.InnerInnerClass.InnerInnerInnerClass.innerInnerMethodCall();
    }
}

class InnerClassContainer {
    class InnerClass {
        public static String methodCall() {
            return "CalledMethod";
        }
        class InnerInnerClass {
            public static String innerMethodCall() {
                return "CalledInnerInnerClass";
            }
            class InnerInnerInnerClass {
                public static String innerInnerMethodCall() {
                    return "CalledInnerInnerInnerClass";
                }
            }
        }
    }
}
