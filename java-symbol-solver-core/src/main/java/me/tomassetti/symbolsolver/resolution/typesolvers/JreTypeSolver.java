package me.tomassetti.symbolsolver.resolution.typesolvers;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;

public class JreTypeSolver implements TypeSolver {

    private TypeSolver parent;

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        if (name.startsWith("java.") || name.startsWith("javax.")) {
            try {
                Class<?> clazz = JreTypeSolver.class.getClassLoader().loadClass(name);
                if (clazz.isInterface()) {
                    return SymbolReference.solved(new ReflectionInterfaceDeclaration(clazz, getRoot()));
                } else {
                    return SymbolReference.solved(new ReflectionClassDeclaration(clazz, getRoot()));
                }
            } catch (ClassNotFoundException e) {
                return SymbolReference.unsolved(TypeDeclaration.class);
            }
        } else {
            return SymbolReference.unsolved(TypeDeclaration.class);
        }
    }

}
