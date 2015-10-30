package me.tomassetti.symbolsolver.resolution.reflection;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.MethodUsage;
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

    public ReflectionMethodDeclaration(Method method) {
        this.method = method;
        if (method.isSynthetic() || method.isBridge()) {
            throw new IllegalArgumentException();
        }
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
            return new ReflectionInterfaceDeclaration(method.getDeclaringClass());
        } else {
            return new ReflectionClassDeclaration(method.getDeclaringClass());
        }
    }

    @Override
    public TypeUsage getReturnType(TypeSolver typeSolver) {
        return ReflectionFactory.typeUsageFor(method.getGenericReturnType());
    }

    @Override
    public int getNoParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i]);
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
        return new MethodUsage(new ReflectionMethodDeclaration(method), typeSolver);
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }
}
