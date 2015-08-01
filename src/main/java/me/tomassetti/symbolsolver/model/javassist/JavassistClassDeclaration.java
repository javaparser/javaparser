package me.tomassetti.symbolsolver.model.javassist;

import javassist.CtClass;
import me.tomassetti.symbolsolver.model.*;

import java.util.List;

/**
 * Created by federico on 01/08/15.
 */
public class JavassistClassDeclaration implements ClassDeclaration {

    private CtClass ctClass;

    public JavassistClassDeclaration(CtClass ctClass) {
        this.ctClass = ctClass;
    }

    @Override
    public String getQualifiedName() {
        return ctClass.getName();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        return ctClass.getSimpleName();
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
        return true;
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        return this;
    }

    @Override
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }
}
