package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtClass;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

public class JavassistParameterDeclaration implements ParameterDeclaration {
    private CtClass type;
    private TypeSolver typeSolver;
    private boolean variadic;

    public JavassistParameterDeclaration(CtClass type, TypeSolver typeSolver, boolean variadic) {
        this.type = type;
        this.typeSolver = typeSolver;
        this.variadic = variadic;
    }

    @Override
    public String toString() {
        return "JavassistParameterDeclaration{" +
                "type=" + type +
                ", typeSolver=" + typeSolver +
                ", variadic=" + variadic +
                '}';
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isVariadic() {
        return variadic;
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Type getType() {
        return JavassistFactory.typeUsageFor(type, typeSolver);
    }
}
