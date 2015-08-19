package me.tomassetti.symbolsolver.model.reflection;

import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

import java.lang.reflect.Field;

/**
 * Created by federico on 19/08/15.
 */
public class ReflectionFieldDeclaration implements FieldDeclaration {

    public ReflectionFieldDeclaration(Field field) {
        this.field = field;
    }

    private Field field;

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        // TODO consider interfaces, enums, primitive types, arrays
        return new ReflectionClassDeclaration(field.getType());
    }

    @Override
    public String getName() {
        return field.getName();
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

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
    }
}
