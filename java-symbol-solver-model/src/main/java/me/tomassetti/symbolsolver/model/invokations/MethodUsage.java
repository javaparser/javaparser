package me.tomassetti.symbolsolver.model.invokations;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.Type;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class MethodUsage {
    private MethodDeclaration declaration;
    private List<Type> paramTypes = new ArrayList<>();
    private Type returnType;

    public MethodUsage(MethodDeclaration declaration) {
        this.declaration = declaration;
        for (int i = 0; i < declaration.getNoParams(); i++) {
            paramTypes.add(declaration.getParam(i).getType());
        }
        returnType = declaration.getReturnType();
    }

    public MethodUsage(MethodDeclaration declaration, List<Type> paramTypes, Type returnType) {
        this.declaration = declaration;
        this.paramTypes = paramTypes;
        this.returnType = returnType;
    }

    private static Type replaceNameParam(String name, Type newValue, Type typeToBeExamined) {
        return typeToBeExamined.replaceParam(name, newValue);
    }

    @Override
    public String toString() {
        return "MethodUsage{" +
                "declaration=" + declaration +
                ", paramTypes=" + paramTypes +
                '}';
    }

    public MethodDeclaration getDeclaration() {
        return declaration;
    }

    public String getName() {
        return declaration.getName();
    }

    public TypeDeclaration declaringType() {
        return declaration.declaringType();
    }

    public Type returnType() {
        return returnType;
    }

    public List<Type> getParamTypes() {
        return paramTypes;
    }

    public MethodUsage replaceParamType(int i, Type replaced) {
        if (paramTypes.get(i) == replaced) {
            return this;
        }
        List<Type> newParams = new LinkedList<>(paramTypes);
        newParams.set(i, replaced);
        return new MethodUsage(declaration, newParams, returnType);
    }

    public MethodUsage replaceReturnType(Type returnType) {
        if (returnType == this.returnType) {
            return this;
        } else {
            return new MethodUsage(declaration, paramTypes, returnType);
        }
    }

    public int getNoParams() {
        return paramTypes.size();
    }

    public Type getParamType(int i) {
        return paramTypes.get(i);
    }

    public MethodUsage replaceNameParam(String name, Type type) {
        if (type == null) {
            throw new IllegalArgumentException();
        }
        // TODO if the method declaration has a type param with that name ignore this call
        MethodUsage res = this;
        for (int i = 0; i < paramTypes.size(); i++) {
            Type originalParamType = paramTypes.get(i);
            Type newParamType = originalParamType.replaceParam(name, type);
            res = res.replaceParamType(i, newParamType);
        }
        res = res.replaceReturnType(replaceNameParam(name, type, res.returnType));
        return res;
    }

}
