package me.tomassetti.symbolsolver.model.usages.typesystem;

/**
 * @author Federico Tomassetti
 */
public class ArrayType implements Type {

    private Type baseType;

    public ArrayType(Type baseType) {
        this.baseType = baseType;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ArrayType that = (ArrayType) o;

        if (!baseType.equals(that.baseType)) return false;

        return true;
    }

    @Override
    public String toString() {
        return "ArrayTypeUsage{" + baseType + "}";
    }

    @Override
    public ArrayType asArrayType() {
        return this;
    }

    @Override
    public int hashCode() {
        return baseType.hashCode();
    }

    @Override
    public boolean isArray() {
        return true;
    }

    @Override
    public String describe() {
        return baseType.describe() + "[]";
    }

    public Type getComponentType() {
        return baseType;
    }

    @Override
    public Type replaceParam(String name, Type replaced) {
        Type baseTypeReplaced = baseType.replaceParam(name, replaced);
        if (baseTypeReplaced == baseType) {
            return this;
        } else {
            return new ArrayType(baseTypeReplaced);
        }
    }

    @Override
    public boolean isAssignableBy(Type other) {
        if (other.isArray()) {
            return baseType.isAssignableBy(other.asArrayType().getComponentType());
        } else {
            return false;
        }
    }

}
