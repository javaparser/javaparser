package me.tomassetti.symbolsolver.model.reflection;


import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;

import java.lang.reflect.TypeVariable;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collector;
import java.util.stream.Collectors;

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
    public List<Bound> getBounds(TypeSolver typeSolver) {
        return Arrays.stream(typeVariable.getBounds()).map((refB)->Bound.extendsBound(ReflectionFactory.typeUsageFor(refB))).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }
}
