package me.tomassetti.symbolsolver.model.reflection;

import me.tomassetti.symbolsolver.model.MethodDeclaration;
import me.tomassetti.symbolsolver.model.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.TypeDeclaration;

import java.lang.reflect.Method;

/**
 * Created by federico on 02/08/15.
 */
public class ReflectionMethodDeclaration implements MethodDeclaration {

    private Method method;

    public ReflectionMethodDeclaration(Method method) {
        this.method = method;
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
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getReturnType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int getNoParams() {
        return method.getParameterTypes().length;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        return new ReflectionParameterDeclaration(method.getParameterTypes()[i]);
    }
}
