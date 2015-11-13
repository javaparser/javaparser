package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.TypeVariable;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ReflectionTypeParameter implements TypeParameter {

    private TypeVariable typeVariable;
    private boolean declaredOnClass;

    public ReflectionTypeParameter(TypeVariable typeVariable, boolean declaredOnClass) {
        this.typeVariable = typeVariable;
        this.declaredOnClass = declaredOnClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TypeParameter)) return false;

        TypeParameter that = (TypeParameter) o;

        if (!getName().equals(that.getName())) {
            return false;
        }
        if (declaredOnClass() != that.declaredOnClass()) {
            return false;
        }
        if (declaredOnMethod() != that.declaredOnMethod()) {
            return false;
        }
        // TODO
        //if (declaredOnClass && !getQNameOfDeclaringClass().equals(that.getQNameOfDeclaringClass())) {
        //    return false;
        //}
        // TODO check bounds
        return true;
    }

    @Override
    public int hashCode() {
        int result = typeVariable.hashCode();
        result = 31 * result + (declaredOnClass ? 1 : 0);
        return result;
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
        return !declaredOnClass;
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
        return Arrays.stream(typeVariable.getBounds()).map((refB) -> Bound.extendsBound(ReflectionFactory.typeUsageFor(refB, typeSolver))).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "ReflectionTypeParameter{" +
                "typeVariable=" + typeVariable +
                '}';
    }
}
