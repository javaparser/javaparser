package me.tomassetti.symbolsolver.model.javassist;

import com.github.javaparser.ast.Node;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Created by federico on 01/08/15.
 */
public class JavassistMethodDeclaration implements MethodDeclaration {
    public JavassistMethodDeclaration(CtMethod ctMethod, TypeSolver typeSolver) {
        this.ctMethod = ctMethod;
        this.typeSolver = typeSolver;
    }

    private CtMethod ctMethod;
    private TypeSolver typeSolver;

    @Override
    public String toString() {
        return "JavassistMethodDeclaration{" +
                "ctMethod=" + ctMethod +
                '}';
    }

    @Override
    public String getName() {
        return ctMethod.getName();
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

    /*@Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType() {
        return new JavassistClassDeclaration(ctMethod.getDeclaringClass());
    }*/

    @Override
    public TypeDeclaration declaringType() {
        return new JavassistClassDeclaration(ctMethod.getDeclaringClass());
    }

    /*            SignatureAttribute.MethodSignature classSignature = SignatureAttribute.toMethodSignature(ctMethod.getGenericSignature());*/

    @Override
    public TypeDeclaration getReturnType() {
        try {
            return new JavassistClassDeclaration(ctMethod.getReturnType());
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public int getNoParams() {
        try {
            return ctMethod.getParameterTypes().length;
        } catch (NotFoundException e){
            throw new RuntimeException(e);
        }
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        try {
            return new JavassistParameterDeclaration(ctMethod.getParameterTypes()[i]);
        } catch (NotFoundException e){
            throw new RuntimeException(e);
        }
    }

    @Override
    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}
