package me.tomassetti.symbolsolver.model.typesystem;

/**
 * This is a virtual type used to represent null values.
 */
public class NullTypeUsage implements TypeUsage {

    public static final NullTypeUsage INSTANCE = new NullTypeUsage();

    private NullTypeUsage() {

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
    public boolean isAssignableBy(TypeUsage other) {
        throw new UnsupportedOperationException("It does not make sense to assign a value to null, it can only be assigned");
    }

}
