package me.tomassetti.symbolsolver.resolution.reflection;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.lang.reflect.Method;

import java.util.Arrays;
import java.util.List;

import java.util.stream.Collectors;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionMethodDeclaration implements MethodDeclaration {

    private Method method;
    private TypeSolver typeSolver;

    public ReflectionMethodDeclaration(Method method, TypeSolver typeSolver) {
        this.method = method;
        if (method.isSynthetic() || method.isBridge()) {
            throw new IllegalArgumentException();
        }
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return method.getName();
    }

    @Override
    public boolean isField() {
        return false;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public String toString() {
        return "ReflectionMethodDeclaration{" +
                "method=" + method +
                '}';
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration declaringType() {
        if (method.getDeclaringClass().isInterface()) {
            return new ReflectionInterfaceDeclaration(method.getDeclaringClass(), typeSolver);
        } else {
            return new ReflectionClassDeclaration(method.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public TypeUsage getReturnType() {
        return ReflectionFactory.typeUsageFor(method.getGenericReturnType(), typeSolver);
    }

    @Override
    public int getNoParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i], typeSolver);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        return Arrays.stream(method.getTypeParameters()).map((refTp)->new ReflectionTypeParameter(refTp, false)).collect(Collectors.toList());
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context, TypeSolver typeSolver, List<TypeUsage> parameterTypes) {
        return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), typeSolver);
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }
}
