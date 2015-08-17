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

    private MethodDeclaration declaration;

    public MethodUsage(MethodDeclaration declaration, TypeSolver typeSolver) {
        this.declaration = declaration;
        for (int i=0;i<declaration.getNoParams();i++){
            paramTypes.add(declaration.getParam(i).getTypeUsage(typeSolver));
        }
        returnType = new TypeUsageOfTypeDeclaration(declaration.getReturnType(typeSolver));
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
}
