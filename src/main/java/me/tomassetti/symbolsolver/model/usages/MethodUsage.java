package me.tomassetti.symbolsolver.model.usages;


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
        //TypeUsage typeUsage = declaration.getParam(i).getType(typeSolver);
        //return typeUsage;
        return paramTypes.get(i);
    }

    public MethodUsage replaceNameParam(String name, TypeUsage typeUsage) {
        // TODO if the method declaration has a type param with that name ignore this call
        MethodUsage res = this;
        for (int i = 0; i<paramTypes.size(); i++){
            TypeUsage originalParamType = paramTypes.get(i);
            TypeUsage newParamType = replaceNameParam(name, typeUsage, originalParamType);
            res = res.replaceParamType(i, newParamType);
        }
        res = res.replaceReturnType(replaceNameParam(name, typeUsage, res.returnType));
        return res;
    }

    private static TypeUsage replaceNameParam(String name, TypeUsage newValue, TypeUsage typeToBeExamined) {
        if (typeToBeExamined.isTypeVariable()){
            if (typeToBeExamined.getTypeName().equals(name)) {
                return newValue;
            } else {
                return typeToBeExamined;
            }
        }
        int i = 0;
        
        return typeToBeExamined;
    }
}
