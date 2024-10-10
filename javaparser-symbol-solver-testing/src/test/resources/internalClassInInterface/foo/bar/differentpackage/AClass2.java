package foo.bar.differentpackage;

import foo.bar.AnInterface;

class AClass {
    static Object field1 = AnInterface.ListChangeType.ADDITION;
    static Object field2 = foo.bar.AnInterface.ListChangeType.ADDITION;
}
