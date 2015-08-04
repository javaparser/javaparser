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
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }
}
