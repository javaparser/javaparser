package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class MethodUsage {
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

    private MethodDeclaration declaration;

    public MethodUsage(MethodDeclaration declaration, TypeSolver typeSolver) {
        this.declaration = declaration;
        for (int i=0;i<declaration.getNoParams();i++){
            paramTypes.add(declaration.getParam(i).getType(typeSolver));
        }
        returnType = declaration.getReturnType(typeSolver);
    }

    public MethodUsage(MethodDeclaration declaration, List<TypeUsage> paramTypes, TypeUsage returnType) {
        this.declaration = declaration;
        this.paramTypes = paramTypes;
        this.returnType = returnType;
    }

    private List<TypeUsage> paramTypes = new ArrayList<>();
    private TypeUsage returnType;

    public String getName() {
        return declaration.getName();
    }

    public TypeDeclaration declaringType() {
        return declaration.declaringType();
    }

    public TypeUsage returnType() {
        return returnType;
    }

    public List<TypeUsage> getParamTypes() {
        return paramTypes;
    }

    public MethodUsage replaceParamType(int i, TypeUsage replaced) {
        if (paramTypes.get(i) == replaced) {
            return this;
        }
        List<TypeUsage> newParams = new LinkedList<>(paramTypes);
        newParams.set(i, replaced);
        return new MethodUsage(declaration, newParams, returnType);
    }

    public MethodUsage replaceReturnType(TypeUsage returnType) {
        if (returnType == this.returnType) {
            return this;
        } else {
            return new MethodUsage(declaration, paramTypes, returnType);
        }
    }

    public int getNoParams() {
        return paramTypes.size();
    }

    public TypeUsage getParamType(int i, TypeSolver typeSolver) {
        TypeUsage typeUsage = declaration.getParam(i).getType(typeSolver);
        return typeUsage;
    }

    public MethodUsage replaceNameParam(String name, TypeUsage typeUsage) {
        // TODO if the method declaration has a type param with that name ignore this call
        // TODO consider return type
        MethodUsage res = this;
        for (int i = 0; i<paramTypes.size(); i++){
            res = replaceParamType(i, replaceNameParam(name, typeUsage, paramTypes.get(i)));
        }
        return res;
    }

    private TypeUsage replaceNameParam(String name, TypeUsage newValue, TypeUsage typeToBeExamined) {
        if (typeToBeExamined.isTypeVariable()){
            if (typeToBeExamined.getTypeName().equals(name)) {
                return newValue;
            } else {
                return typeToBeExamined;
            }
        }
        int i = 0;
        for (TypeUsage param : typeToBeExamined.parameters()) {
            typeToBeExamined = typeToBeExamined.replaceParam(i, replaceNameParam(name, newValue, typeToBeExamined.parameters().get(i)));
            i++;
        }
        return typeToBeExamined;
    }
}
