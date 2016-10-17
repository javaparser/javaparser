package me.tomassetti.symbolsolver.model.usages.typesystem;

import com.google.common.collect.ImmutableList;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class PrimitiveType implements Type {

    public static final PrimitiveType BYTE = new PrimitiveType("byte", Byte.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveType SHORT = new PrimitiveType("short", Short.class.getCanonicalName(), ImmutableList.of(BYTE));
    public static final PrimitiveType INT = new PrimitiveType("int", Integer.class.getCanonicalName(), ImmutableList.of(BYTE, SHORT));
    public static final PrimitiveType LONG = new PrimitiveType("long", Long.class.getCanonicalName(), ImmutableList.of(BYTE, SHORT, INT));
    public static final PrimitiveType CHAR = new PrimitiveType("char", Character.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveType BOOLEAN = new PrimitiveType("boolean", Boolean.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveType FLOAT = new PrimitiveType("float", Float.class.getCanonicalName(), ImmutableList.of());
    public static final PrimitiveType DOUBLE = new PrimitiveType("double", Double.class.getCanonicalName(), ImmutableList.of(FLOAT));
    public static final List<PrimitiveType> ALL = ImmutableList.of(INT, BOOLEAN, LONG, CHAR, FLOAT, DOUBLE, SHORT, BYTE);
    private String name;
    private String boxTypeQName;
    private List<PrimitiveType> promotionTypes;

    private PrimitiveType(String name, String boxTypeQName, List<PrimitiveType> promotionTypes) {
        this.name = name;
        this.boxTypeQName = boxTypeQName;
        this.promotionTypes = promotionTypes;
    }

    public static Type byName(String name) {
        name = name.toLowerCase();
        for (PrimitiveType ptu : ALL) {
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

    public PrimitiveType asPrimitive() {
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
    public boolean isAssignableBy(Type other) {
        if (other.isPrimitive()) {
            return this == other || promotionTypes.contains(other);
        } else if (other.isReferenceType()) {
            if (other.asReferenceType().getQualifiedName().equals(boxTypeQName)) {
                return true;
            }
            for (PrimitiveType promotion : promotionTypes) {
                if (other.asReferenceType().getQualifiedName().equals(promotion.boxTypeQName)) {
                    return true;
                }
            }
            return false;
        } else {
            return false;
        }
    }

}
