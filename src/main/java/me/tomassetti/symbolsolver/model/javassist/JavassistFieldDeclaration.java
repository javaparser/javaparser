package me.tomassetti.symbolsolver.model.javassist;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import javassist.CtField;
import javassist.CtMethod;
import javassist.NotFoundException;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;

import java.util.List;

/**
 * Created by federico on 01/08/15.
 */
public class JavassistFieldDeclaration implements me.tomassetti.symbolsolver.model.FieldDeclaration {
    public JavassistFieldDeclaration(CtField ctField, TypeSolver typeSolver) {
        this.ctField = ctField;
        this.typeSolver = typeSolver;
    }

    private CtField ctField;
    private TypeSolver typeSolver;

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
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

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
    }
}
