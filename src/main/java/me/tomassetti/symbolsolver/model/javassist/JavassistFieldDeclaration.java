package me.tomassetti.symbolsolver.model.javassist;

import javassist.CtField;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.TypeSolver;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

/**
 * Created by federico on 01/08/15.
 */
public class JavassistFieldDeclaration implements me.tomassetti.symbolsolver.model.declarations.FieldDeclaration {
    public JavassistFieldDeclaration(CtField ctField, TypeSolver typeSolver) {
        this.ctField = ctField;
        this.typeSolver = typeSolver;
    }

    private CtField ctField;
    private TypeSolver typeSolver;

    @Override
    public TypeUsage getType(TypeSolver typeSolver) {
        try {
            return JavassistFactory.typeUsageFor(ctField.getType());
        } catch (NotFoundException e){
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
