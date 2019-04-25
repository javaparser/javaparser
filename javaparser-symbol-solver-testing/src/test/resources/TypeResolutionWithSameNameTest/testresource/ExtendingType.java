package testresource;

public class ExtendingType implements DuplicateTypeName {
    class DuplicateTypeName extends ExtendingType {

    }
}