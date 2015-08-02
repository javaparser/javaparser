package me.tomassetti.symbolsolver.model.javassist;

import com.github.javaparser.ast.Node;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.*;

import java.util.List;

/**
 * Created by federico on 01/08/15.
 */
public class JavassistClassDeclaration implements ClassDeclaration {

    private CtClass ctClass;

    public JavassistClassDeclaration(CtClass ctClass) {
        if (ctClass == null) {
            throw new IllegalArgumentException();
        }
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

        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)){
                // TODO check parameters
                return SymbolReference.solved(new JavassistMethodDeclaration(method));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(superClass).solveMethod(name, parameterTypes);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(interfaze).solveMethod(name, parameterTypes);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        return SymbolReference.unsolved(MethodDeclaration.class);
    }

    @Override
    public TypeUsage getUsage(Node node) {
        return new TypeUsageOfTypeDeclaration(getType());
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
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
