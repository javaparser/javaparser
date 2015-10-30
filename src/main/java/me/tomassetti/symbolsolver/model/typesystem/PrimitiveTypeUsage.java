package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.util.List;

public class PrimitiveTypeUsage implements TypeUsage {

    private String name;

    public static final PrimitiveTypeUsage INT = new PrimitiveTypeUsage("int");
    public static final PrimitiveTypeUsage CHAR = new PrimitiveTypeUsage("char");
    public static final PrimitiveTypeUsage LONG = new PrimitiveTypeUsage("long");
    public static final PrimitiveTypeUsage BOOLEAN = new PrimitiveTypeUsage("boolean");
    public static final PrimitiveTypeUsage FLOAT = new PrimitiveTypeUsage("float");
    public static final PrimitiveTypeUsage DOUBLE = new PrimitiveTypeUsage("double");
    public static final PrimitiveTypeUsage SHORT = new PrimitiveTypeUsage("short");
    public static final PrimitiveTypeUsage BYTE = new PrimitiveTypeUsage("byte");

    @Override
    public String toString() {
        return "PrimitiveTypeUsage{" +
                "name='" + name + '\'' +
                '}';
    }

    public static final List<PrimitiveTypeUsage> ALL = ImmutableList.of(INT, BOOLEAN, LONG, CHAR, FLOAT, DOUBLE, SHORT, BYTE);

    private PrimitiveTypeUsage(String name) {
        this.name = name;
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

    public static TypeUsage byName(String name) {
        name = name.toLowerCase();
        for (PrimitiveTypeUsage ptu : ALL) {
            if (ptu.describe().equals(name)) {
                return ptu;
            }
        }
        throw new IllegalArgumentException("Name "+name);
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (other instanceof PrimitiveTypeUsage) {
            return name.equals(((PrimitiveTypeUsage) other).name);
        } else {
            return false;
        }
    }

}
