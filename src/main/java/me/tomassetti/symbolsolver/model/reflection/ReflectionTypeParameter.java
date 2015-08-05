package me.tomassetti.symbolsolver.model.reflection;


import me.tomassetti.symbolsolver.model.TypeParameter;

import java.lang.reflect.TypeVariable;

public class ReflectionTypeParameter implements TypeParameter {

    private TypeVariable typeVariable;
    private boolean declaredOnClass;

    public ReflectionTypeParameter(TypeVariable typeVariable, boolean declaredOnClass) {
        this.typeVariable = typeVariable;
        this.declaredOnClass = declaredOnClass;
    }

    @Override
    public String getName() {
        return typeVariable.getName();
    }

    @Override
    public boolean declaredOnClass() {
        return declaredOnClass;
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
