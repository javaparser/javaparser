package me.tomassetti.symbolsolver.resolution.typesolvers;

import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;

/**
 * Created by federico on 01/08/15.
 */
public class JreTypeSolver implements TypeSolver {

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        if (name.startsWith("java.") || name.startsWith("javax.")) {
            try {
                Class<?> clazz = JreTypeSolver.class.getClassLoader().loadClass(name);
                if (clazz.isInterface()) {
                    return SymbolReference.solved(new ReflectionInterfaceDeclaration(clazz));
                } else {
                    return SymbolReference.solved(new ReflectionClassDeclaration(clazz));
                }
            } catch (ClassNotFoundException e){
                return SymbolReference.unsolved(TypeDeclaration.class);
            }
        } else {
            return SymbolReference.unsolved(TypeDeclaration.class);
        }
    }

}
