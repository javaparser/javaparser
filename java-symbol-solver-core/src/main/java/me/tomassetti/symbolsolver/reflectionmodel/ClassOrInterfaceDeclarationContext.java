package me.tomassetti.symbolsolver.reflectionmodel;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.List;

public class ClassOrInterfaceDeclarationContext implements Context {

    private Class<?> wrapped;

    public ClassOrInterfaceDeclarationContext(Class<?> clazz) {
        this.wrapped = clazz;
    }


    @Override
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {
        for (Field field : wrapped.getFields()) {
            if (Modifier.isStatic(field.getModifiers()) && field.getName().equals(name)) {
                if (field.getDeclaringClass().getCanonicalName().equals(wrapped.getCanonicalName())
                        || !Modifier.isPrivate(field.getModifiers())) {
                    return SymbolReference.solved(new ReflectionFieldDeclaration(field, typeSolver));
                }
            }
        }
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Context getParent() {
        throw new UnsupportedOperationException();
    }

}
