package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.TypeParameter;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.*;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

public class JavaParserTypeVariableDeclaration extends AbstractTypeDeclaration {

    private TypeParameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeVariableDeclaration(TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public String getQualifiedName() {
        return getName();
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
        return "JavaParserTypeVariableDeclaration{" +
                wrappedNode.getName() +
                '}';
    }

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

    public Type getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(Type type) {
        if (type.isTypeVariable()) {
            throw new UnsupportedOperationException("Is this type variable declaration assignable by " + type.describe());
        } else {
            throw new UnsupportedOperationException("Is this type variable declaration assignable by " + type);
        }
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public FieldDeclaration getField(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name) {
        return false;
    }

    @Override
    public List<FieldDeclaration> getAllFields() {
        return new ArrayList<>();
    }

    @Override
    public List<ReferenceType> getAncestors() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Collections.emptySet();
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isType() {
        return true;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    public TypeParameterDeclaration asTypeParameter() {
        return new JavaParserTypeParameter(this.wrappedNode, typeSolver);
    }

	/**
	 * Returns the JavaParser node associated with this JavaParserTypeVariableDeclaration.
	 *
	 * @return A visitable JavaParser node wrapped by this object.
	 */
	public TypeParameter getWrappedNode()
	{
		return wrappedNode;
	}
}
