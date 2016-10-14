package me.tomassetti.symbolsolver.model.usages.typesystem;

/**
 * This is a virtual type used to represent null values.
 *
 * @author Federico Tomassetti
 */
public class NullType implements Type {

    public static final NullType INSTANCE = new NullType();

    private NullType() {
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return false;
    }

    public boolean isNull() {
        return true;
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
        return "null";
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public boolean isAssignableBy(Type other) {
        throw new UnsupportedOperationException("It does not make sense to assign a value to null, it can only be assigned");
    }

}
