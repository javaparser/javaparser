package me.tomassetti.symbolsolver.model.reflection;


import me.tomassetti.symbolsolver.model.TypeParameter;

import java.lang.reflect.TypeVariable;

public class ReflectionTypeParameter implements TypeParameter {

    private TypeVariable typeVariable;

    public ReflectionTypeParameter(TypeVariable typeVariable) {
        this.typeVariable = typeVariable;
    }

    @Override
    public String getName() {
        return typeVariable.getName();
    }

    @Override
    public boolean declaredOnClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean declaredOnMethod() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }
}
