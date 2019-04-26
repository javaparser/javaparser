package testresource;

public class A implements DuplicateTypeName {
    class DuplicateTypeName extends A {

    }
}
