package me.tomassetti.symbolsolver.resolution.reflection;

import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.lang.reflect.Type;

public class ReflectionParameterDeclaration implements ParameterDeclaration {
    private Class<?> type;
    private Type genericType;
    private TypeSolver typeSolver;

    public ReflectionParameterDeclaration(Class<?> type, Type genericType, TypeSolver typeSolver) {
        this.type = type;
        this.genericType = genericType;
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
        return "ReflectionParameterDeclaration{" +
                "type=" + type +
                '}';
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return true;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeUsage getType() {
        return ReflectionFactory.typeUsageFor(genericType, typeSolver);
    }
}
