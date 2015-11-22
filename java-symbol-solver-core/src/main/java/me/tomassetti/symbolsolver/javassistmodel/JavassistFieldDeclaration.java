package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtField;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

public class JavassistFieldDeclaration implements me.tomassetti.symbolsolver.model.declarations.FieldDeclaration {
    private CtField ctField;
    private TypeSolver typeSolver;
    public JavassistFieldDeclaration(CtField ctField, TypeSolver typeSolver) {
        this.ctField = ctField;
        this.typeSolver = typeSolver;
    }

    @Override
    public TypeUsage getType() {
        try {
            return JavassistFactory.typeUsageFor(ctField.getType(), typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public String getName() {
        return ctField.getName();
    }

    @Override
    public boolean isField() {
        return true;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }
}
