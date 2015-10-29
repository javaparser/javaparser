package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.Collections;
import java.util.List;

/**
 * Created by federico on 18/08/15.
 */
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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeUsage> parameters() {
        return Collections.emptyList();
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
    public boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver) {
        if (other instanceof PrimitiveTypeUsage) {
            return name.equals(((PrimitiveTypeUsage) other).name);
        } else {
            return false;
        }
    }

    @Override
    public String getQualifiedName() {
        return name;
    }

    @Override
    public String prettyPrint() {
        return name;
    }
}
