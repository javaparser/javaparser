package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

public class MethodUsage {

    private MethodDeclaration declaration;

    public MethodUsage(MethodDeclaration declaration) {
        this.declaration = declaration;
    }

    public MethodUsage(SymbolReference<MethodDeclaration> ref) {
        this(ref.getCorrespondingDeclaration());
    }

    public String getName() {
        return declaration.getName();
    }

    public TypeDeclaration declaringType() {
        return declaration.declaringType();
    }
}
