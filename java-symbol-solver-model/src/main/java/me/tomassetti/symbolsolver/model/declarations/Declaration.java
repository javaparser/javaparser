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
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default MethodDeclaration asMethod() {
        throw new UnsupportedOperationException();
    }
}
