package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.List;

/**
 * @author Federico Tomassetti
 */
public class JavaParserConstructorDeclaration implements ConstructorDeclaration {

    private ClassDeclaration classDeclaration;
    private com.github.javaparser.ast.body.ConstructorDeclaration wrapped;
    private TypeSolver typeSolver;

    public JavaParserConstructorDeclaration(ClassDeclaration classDeclaration, com.github.javaparser.ast.body.ConstructorDeclaration wrapped,
                                            TypeSolver typeSolver) {
        this.classDeclaration = classDeclaration;
        this.wrapped = wrapped;
        this.typeSolver = typeSolver;
    }

    @Override
    public ClassDeclaration declaringType() {
        return classDeclaration;
    }

    @Override
    public int getNoParams() {
        return this.wrapped.getParameters().size();
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        if (i < 0 || i >= getNoParams()) {
            throw new IllegalArgumentException(String.format("No param with index %d. Number of params: %d", i, getNoParams()));
        }
        return new JavaParserParameterDeclaration(wrapped.getParameters().get(i), typeSolver);
    }

    @Override
    public String getName() {
        return this.classDeclaration.getName();
    }

    @Override
    public AccessLevel accessLevel() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        throw new UnsupportedOperationException();
    }
}