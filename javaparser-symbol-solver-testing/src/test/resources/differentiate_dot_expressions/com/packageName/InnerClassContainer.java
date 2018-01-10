public class InnerClassContainer {
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
