package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.resolution.declarations.ResolvedEnumConstantDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Field;

public class ReflectionEnumConstantDeclaration implements ResolvedEnumConstantDeclaration {

    private Field enumConstant;
    private TypeSolver typeSolver;

    public ReflectionEnumConstantDeclaration(Field enumConstant, TypeSolver typeSolver) {
        if (!enumConstant.isEnumConstant()) {
            throw new IllegalArgumentException("The given field does not represent an enum constant");
        }
        this.enumConstant = enumConstant;
        this.typeSolver = typeSolver;
    }

    @Override
    public String getName() {
        return enumConstant.getName();
    }

    @Override
    public ResolvedType getType() {
        throw new UnsupportedOperationException();
    }
}
