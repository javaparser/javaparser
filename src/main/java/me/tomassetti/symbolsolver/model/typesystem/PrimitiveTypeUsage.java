package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;

import java.util.List;

public class PrimitiveTypeUsage implements TypeUsage {

    public static final PrimitiveTypeUsage BYTE = new PrimitiveTypeUsage("byte", Byte.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveTypeUsage SHORT = new PrimitiveTypeUsage("short", Short.class.getCanonicalName(), ImmutableList.of(BYTE));
    public static final PrimitiveTypeUsage INT = new PrimitiveTypeUsage("int", Integer.class.getCanonicalName(), ImmutableList.of(BYTE, SHORT));
    public static final PrimitiveTypeUsage LONG = new PrimitiveTypeUsage("long", Long.class.getCanonicalName(), ImmutableList.of(BYTE, SHORT, INT));
    public static final PrimitiveTypeUsage CHAR = new PrimitiveTypeUsage("char", Character.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveTypeUsage BOOLEAN = new PrimitiveTypeUsage("boolean", Boolean.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveTypeUsage FLOAT = new PrimitiveTypeUsage("float", Float.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveTypeUsage DOUBLE = new PrimitiveTypeUsage("double", Double.class.getCanonicalName(), ImmutableList.of(FLOAT));
    public static final List<PrimitiveTypeUsage> ALL = ImmutableList.of(INT, BOOLEAN, LONG, CHAR, FLOAT, DOUBLE, SHORT, BYTE);
    private String name;
    private String boxTypeQName;
    private List<PrimitiveTypeUsage> promotionTypes;

    private PrimitiveTypeUsage(String name, String boxTypeQName, List<PrimitiveTypeUsage> promotionTypes) {
        this.name = name;
        this.boxTypeQName = boxTypeQName;
        this.promotionTypes = promotionTypes;
    }

    public static TypeUsage byName(String name) {
        name = name.toLowerCase();
        for (PrimitiveTypeUsage ptu : ALL) {
            if (ptu.describe().equals(name)) {
                return ptu;
            }
        }
        throw new IllegalArgumentException("Name " + name);
    }

    @Override
    public String toString() {
        return "PrimitiveTypeUsage{" +
                "name='" + name + '\'' +
                '}';
    }

    public PrimitiveTypeUsage asPrimitive() {
        return this;
    }

    @Override
    public boolean isArray() {
        return false;
    }

    @Override
    public boolean isPrimitive() {
        return true;
    }

    @Override
    public boolean isReferenceType() {
        return false;
    }

    @Override
    public String describe() {
        return name;
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (other.isPrimitive()) {
            return this == other || promotionTypes.contains(other);
        } else if (other.isReferenceType()) {
            if (other.asReferenceTypeUsage().getQualifiedName().equals(boxTypeQName)) {
                return true;
            }
            for (PrimitiveTypeUsage promotion : promotionTypes) {
                if (other.asReferenceTypeUsage().getQualifiedName().equals(promotion.boxTypeQName)) {
                    return true;
                }
            }
            return false;
        } else {
            return false;
        }
    }

}
