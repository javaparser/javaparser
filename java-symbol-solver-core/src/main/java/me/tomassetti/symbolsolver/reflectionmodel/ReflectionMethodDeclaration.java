package me.tomassetti.symbolsolver.reflectionmodel;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

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
        boolean variadic = false;
        if (method.isVarArgs()) {
            variadic = i == (method.getParameterCount() - 1);
        }
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i], method.getGenericParameterTypes()[i], typeSolver, variadic);
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        return Arrays.stream(method.getTypeParameters()).map((refTp) -> new ReflectionTypeParameter(refTp, false)).collect(Collectors.toList());
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context, List<TypeUsage> parameterTypes) {
        return new MethodUsage(new ReflectionMethodDeclaration(method, typeSolver), typeSolver);
    }

    @Override
    public boolean isAbstract() {
        return Modifier.isAbstract(method.getModifiers());
    }

    @Override
    public boolean isPrivate() {
        return Modifier.isPrivate(method.getModifiers());
    }

    @Override
    public boolean isPackageProtected() {
        return !Modifier.isPrivate(method.getModifiers()) && !Modifier.isProtected(method.getModifiers()) && !Modifier.isPublic(method.getModifiers());
    }

}
