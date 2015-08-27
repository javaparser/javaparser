package me.tomassetti.symbolsolver.model.reflection;

import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;

import me.tomassetti.symbolsolver.model.usages.TypeUsage;


import java.lang.reflect.Type;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionParameterDeclaration implements ParameterDeclaration {
    private Class<?> type;
    private Type genericType;

    public ReflectionParameterDeclaration(Class<?> type, Type genericType) {
        this.type = type;
        this.genericType = genericType;
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
    public TypeUsage getType(TypeSolver typeSolver) {
        return ReflectionFactory.typeUsageFor(genericType);
    }
}
