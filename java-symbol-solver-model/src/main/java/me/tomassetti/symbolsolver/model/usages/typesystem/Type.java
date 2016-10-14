package me.tomassetti.symbolsolver.model.usages.typesystem;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;

/**
 * A usage of a type. It could be a primitive type or a reference type (enum, class, interface).
 * In the later case it could take type parameters (other TypeUsages). It could also be a TypeVariable, like in:
 * <p/>
 * class A<B> { }
 * <p/>
 * where B is a TypeVariable. It could also be Wildcard Type, possibly with constraints.
 *
 * @author Federico Tomassetti
 */
public interface Type {

    ///
    /// Relation with other types
    ///

    /**
     * Does this type represent an array?
     */
    default boolean isArray() {
        return false;
    }

    default int arrayLevel() {
        if (isArray()) {
            return 1 + this.asArrayTypeUsage().getComponentType().arrayLevel();
        } else {
            return 0;
        }
    }

    /**
     * Is this a primitive type?
     */
    default boolean isPrimitive() {
        return false;
    }

    /**
     * Is this the null type?
     */
    default boolean isNull() {
        return false;
    }

    /**
     * Is this a non primitive value?
     */
    default boolean isReference() {
        return isReferenceType() || isArray() || isTypeVariable() || isNull();
    }

    /**
     * Can this be seen as a ReferenceTypeUsage?
     * In other words: is this a reference to a class, an interface or an enum?
     */
    default boolean isReferenceType() {
        return false;
    }

    default boolean isVoid() {
        return false;
    }

    default boolean isTypeVariable() {
        return false;
    }

    default boolean isWildcard() {
        return false;
    }

    ///
    /// Downcasting
    ///

    default ArrayType asArrayTypeUsage() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default ReferenceType asReferenceTypeUsage() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeParameterDeclaration asTypeParameter() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default PrimitiveType asPrimitive() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default Wildcard asWildcard() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    ///
    /// Naming
    ///

    String describe();

    ///
    /// TypeParameters
    ///

    default Type replaceParam(String name, Type replaced) {
        return this;
    }

    ///
    /// Relation with other types
    ///
    
    /**
     * This method checks if ThisType t = new OtherType() would compile.
     */
    boolean isAssignableBy(Type other);

}
