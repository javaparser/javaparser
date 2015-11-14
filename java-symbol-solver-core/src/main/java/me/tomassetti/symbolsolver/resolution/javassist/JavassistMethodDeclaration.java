package me.tomassetti.symbolsolver.resolution.javassist;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ModifierSet;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.SignatureAttribute;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class JavassistMethodDeclaration implements MethodDeclaration {
    private CtMethod ctMethod;
    private TypeSolver typeSolver;
    public JavassistMethodDeclaration(CtMethod ctMethod, TypeSolver typeSolver) {
        this.ctMethod = ctMethod;
        this.typeSolver = typeSolver;
    }

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
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public TypeDeclaration declaringType() {
        if (ctMethod.getDeclaringClass().isInterface()) {
            return new JavassistInterfaceDeclaration(ctMethod.getDeclaringClass(), typeSolver);
        } else {
            return new JavassistClassDeclaration(ctMethod.getDeclaringClass(), typeSolver);
        }
    }

    @Override
    public TypeUsage getReturnType() {
        try {
            return JavassistFactory.typeUsageFor(ctMethod.getReturnType(), typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }


    @Override
    public int getNoParams() {
        try {
            return ctMethod.getParameterTypes().length;
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        try {
            return new JavassistParameterDeclaration(ctMethod.getParameterTypes()[i], typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    public MethodUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MethodUsage resolveTypeVariables(Context context, List<TypeUsage> parameterTypes) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAbstract() {
        return ModifierSet.isAbstract(ctMethod.getModifiers());
    }

    @Override
    public boolean isPrivate() {
        return ModifierSet.isPrivate(ctMethod.getModifiers());
    }

    @Override
    public boolean isPackageProtected() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        try {
            if (ctMethod.getGenericSignature() == null) {
                return Collections.emptyList();
            }
            SignatureAttribute.MethodSignature methodSignature = SignatureAttribute.toMethodSignature(ctMethod.getGenericSignature());
            return Arrays.stream(methodSignature.getTypeParameters()).map((jasTp) -> new JavassistTypeParameter(jasTp, false, typeSolver)).collect(Collectors.toList());
        } catch (BadBytecode badBytecode) {
            throw new RuntimeException(badBytecode);
        }
    }
}
