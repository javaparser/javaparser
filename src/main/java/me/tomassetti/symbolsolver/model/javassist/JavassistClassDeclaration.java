package me.tomassetti.symbolsolver.model.javassist;

import com.github.javaparser.ast.Node;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

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
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {

        for (CtMethod method : ctClass.getDeclaredMethods()) {
            if (method.getName().equals(name)){
                // TODO check parameters
                return SymbolReference.solved(new JavassistMethodDeclaration(method));
            }
        }

        try {
            CtClass superClass = ctClass.getSuperclass();
            if (superClass != null) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(superClass).solveMethod(name, parameterTypes, typeSolver);
                if (ref.isSolved()) {
                    return ref;
                }
            }
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }

        try {
            for (CtClass interfaze : ctClass.getInterfaces()) {
                SymbolReference<MethodDeclaration> ref = new JavassistClassDeclaration(interfaze).solveMethod(name, parameterTypes, typeSolver);
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
        return new TypeUsageOfTypeDeclaration(this);
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeVariable() {
        return false;
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
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

    /*@Override
    public TypeDeclaration asTypeDeclaration() {
        return this;
    }

    @Override
    public TypeDeclaration getType() {
        throw new UnsupportedOperationException();
    }*/

    @Override
    public List<TypeParameter> getTypeParameters() {
        if (null == ctClass.getGenericSignature()) {
            return Collections.emptyList();
        } else {
            try {
                SignatureAttribute.ClassSignature classSignature = SignatureAttribute.toClassSignature(ctClass.getGenericSignature());
                System.out.println("Type params" + classSignature.getParameters());
                return Arrays.<SignatureAttribute.TypeParameter>stream(classSignature.getParameters()).map((tp)->new JavassistTypeParameter(tp)).collect(Collectors.toList());
            } catch (BadBytecode badBytecode) {
                throw new RuntimeException(badBytecode);
            }
        }
    }
}
