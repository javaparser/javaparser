package me.tomassetti.symbolsolver.logic;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;

import java.util.HashSet;
import java.util.Set;

public abstract class AbstractTypeDeclaration implements TypeDeclaration {

    protected abstract TypeSolver typeSolver();

    @Override
    public Set<MethodUsage> getAllMethods() {
        Set<MethodUsage> methods = new HashSet<>();

        Set<String> methodsSignatures = new HashSet<>();

        for (MethodDeclaration methodDeclaration : getDeclaredMethods()) {
            methods.add(new MethodUsage(methodDeclaration));
            methodsSignatures.add(methodDeclaration.getSignature());
        }

        for (ReferenceType ancestor : getAllAncestors()) {
            for (MethodUsage mu : ancestor.getDeclaredMethods()) {
                String signature = mu.getDeclaration().getSignature();
                if (!methodsSignatures.contains(signature)) {
                    methodsSignatures.add(signature);
                    methods.add(mu);
                }
            }
        }

        return methods;
    }

}
