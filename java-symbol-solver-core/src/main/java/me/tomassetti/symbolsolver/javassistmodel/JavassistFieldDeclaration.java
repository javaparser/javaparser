package me.tomassetti.symbolsolver.javassistmodel;

import javassist.CtField;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.declarations.AccessLevel;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.lang.reflect.Modifier;

public class JavassistFieldDeclaration implements me.tomassetti.symbolsolver.model.declarations.FieldDeclaration {
    private CtField ctField;
    private TypeSolver typeSolver;
    public JavassistFieldDeclaration(CtField ctField, TypeSolver typeSolver) {
        this.ctField = ctField;
        this.typeSolver = typeSolver;
    }

    @Override
    public Type getType() {
        try {
            return JavassistFactory.typeUsageFor(ctField.getType(), typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean isStatic() {
        return Modifier.isStatic(ctField.getModifiers());
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
    public boolean isType() {
        return false;
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration declaringType() {
        throw new UnsupportedOperationException();
    }
}
