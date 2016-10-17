package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import me.tomassetti.symbolsolver.model.declarations.*;

import java.util.Collections;
import java.util.List;

/**
 * @author Federico Tomassetti
 */
class DefaultConstructorDeclaration implements ConstructorDeclaration {

    private ClassDeclaration classDeclaration;

    DefaultConstructorDeclaration(ClassDeclaration classDeclaration) {
        this.classDeclaration = classDeclaration;
    }

    @Override
    public ClassDeclaration declaringType() {
        return classDeclaration;
    }

    @Override
    public int getNoParams() {
        return 0;
    }

    @Override
    public ParameterDeclaration getParam(int i) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public AccessLevel accessLevel() {
        return AccessLevel.PUBLIC;
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }
}
