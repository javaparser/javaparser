package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.GenericDeclaration;
import java.lang.reflect.TypeVariable;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class ReflectionTypeParameter implements TypeParameterDeclaration {

    private TypeVariable typeVariable;
    private boolean declaredOnClass;
    private String qNameOfDeclaringClass;

    public ReflectionTypeParameter(TypeVariable typeVariable, boolean declaredOnClass) {
        GenericDeclaration genericDeclaration = typeVariable.getGenericDeclaration();
        if (genericDeclaration instanceof Class) {
            Class clazz = (Class)genericDeclaration;
            qNameOfDeclaringClass = clazz.getTypeName();
        } else {
            //System.out.println(genericDeclaration.getClass().getCanonicalName());
            qNameOfDeclaringClass = null;
        }
        this.typeVariable = typeVariable;
        this.declaredOnClass = declaredOnClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TypeParameterDeclaration)) return false;

        TypeParameterDeclaration that = (TypeParameterDeclaration) o;

        if (!getName().equals(that.getName())) {
            return false;
        }
        if (declaredOnClass() != that.declaredOnClass()) {
            return false;
        }
        if (declaredOnMethod() != that.declaredOnMethod()) {
            return false;
        }
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
    public String getQualifiedName() {
        if (this.declaredOnClass()) {
            return String.format("%s.%s", qNameOfDeclaringClass, getName());
        } else {
            throw new UnsupportedOperationException(typeVariable.getGenericDeclaration().getClass().getCanonicalName());
            //typeVariable.getGenericDeclaration()
            //com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration)wrappedNode.getParentNode();
            //MethodDeclaration methodDeclaration = new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver());
            //return String.format("%s.%s", methodDeclaration.getQualifiedSignature(), getName());
        }
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
