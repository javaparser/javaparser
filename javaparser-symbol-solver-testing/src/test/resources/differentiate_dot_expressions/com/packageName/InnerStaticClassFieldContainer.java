package com.packageName;

public class InnerStaticClassFieldContainer {
    static class InnerClass {
        public static String methodCall() {
            return "CalledMethod";
        }
        static class InnerInnerClass {
            public static final String MY_INT = "1";
            public static String innerMethodCall() {
                return "CalledInnerInnerClass";
            }
        }
    }
}
