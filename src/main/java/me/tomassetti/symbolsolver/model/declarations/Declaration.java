package me.tomassetti.symbolsolver.model.declarations;

/**
 * A generic declaration.
 */
public interface Declaration {

    /**
     * Anonymous classes do not have a name, for example.

     */
    default boolean hasName() {
        return true;
    }

    String getName();

    default boolean isField() {
        return false;
    }

    default boolean isParameter() {
        return false;
    }

    default boolean isVariable() {
        return false;
    }

    default boolean isType() {
        return false;
    }

    default boolean isMethod() {
        return false;
    }

    default FieldDeclaration asField() {
        throw new UnsupportedOperationException();
    }

    default ParameterDeclaration asParameter() {
        throw new UnsupportedOperationException();
    }

    default TypeDeclaration asType() {
        throw new UnsupportedOperationException();
    }

    default MethodDeclaration asMethod() {
        throw new UnsupportedOperationException();
    }
}
