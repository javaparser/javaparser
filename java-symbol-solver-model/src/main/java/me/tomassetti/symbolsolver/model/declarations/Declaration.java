package me.tomassetti.symbolsolver.model.declarations;

/**
 * A generic declaration.
 *
 * @author Federico Tomassetti
 */
public interface Declaration {

    /**
     * Anonymous classes do not have a name, for example.
     */
    default boolean hasName() {
        return true;
    }

    /**
     * Should return the name or throw a RuntimeException if the name is not available.
     */
    String getName();

    default boolean isField() {
        return false;
    }

    default boolean isParameter() {
        return false;
    }

    default boolean isType() {
        return false;
    }

    default boolean isMethod() {
        return false;
    }

    default FieldDeclaration asField() {
        throw new UnsupportedOperationException(String.format("%s is not a FieldDeclaration", this));
    }

    default ParameterDeclaration asParameter() {
        throw new UnsupportedOperationException(String.format("%s is not a ParameterDeclaration", this));
    }

    default TypeDeclaration asType() {
        throw new UnsupportedOperationException(String.format("%s is not a TypeDeclaration", this));
    }

    default MethodDeclaration asMethod() {
        throw new UnsupportedOperationException(String.format("%s is not a MethodDeclaration", this));
    }
}
