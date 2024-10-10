package main;

import static main.Main.NestedEnum.*;

public class Main {

    public Main() {
        foo();
        NestedEnum.bar();
        NestedEnum c;
        c.baz();
    }

    public enum NestedEnum {
        ;
        public static void foo() {}
        public static void bar() {}
        public void baz() {}
    }
}
