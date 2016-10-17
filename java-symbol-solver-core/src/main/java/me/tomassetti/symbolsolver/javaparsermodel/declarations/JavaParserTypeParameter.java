package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import me.tomassetti.symbolsolver.core.resolution.Context;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceType;
import me.tomassetti.symbolsolver.model.usages.typesystem.ReferenceTypeImpl;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class JavaParserTypeParameter extends AbstractTypeDeclaration implements TypeParameterDeclaration {

    private com.github.javaparser.ast.TypeParameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeParameter(com.github.javaparser.ast.TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    @Override
    public Set<MethodDeclaration> getDeclaredMethods() {
        return Collections.emptySet();
    }

    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes) {
        return getContext().solveMethod(name, parameterTypes, typeSolver());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof JavaParserTypeParameter)) return false;

        JavaParserTypeParameter that = (JavaParserTypeParameter) o;

        if (wrappedNode != null ? !wrappedNode.equals(that.wrappedNode) : that.wrappedNode != null) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = wrappedNode != null ? wrappedNode.hashCode() : 0;
        result = 31 * result + (typeSolver != null ? typeSolver.hashCode() : 0);
        return result;
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeImpl(other, typeSolver));
    }

    @Override
    public boolean declaredOnClass() {
        return (wrappedNode.getParentNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Override
    public boolean declaredOnMethod() {
        return wrappedNode.getParentNode() instanceof com.github.javaparser.ast.body.MethodDeclaration;
    }

    @Override
    public String getQualifiedName() {
        if (this.declaredOnClass()) {
            com.github.javaparser.ast.body.ClassOrInterfaceDeclaration jpTypeDeclaration = (com.github.javaparser.ast.body.ClassOrInterfaceDeclaration)wrappedNode.getParentNode();
            TypeDeclaration typeDeclaration = JavaParserFacade.get(typeSolver).getTypeDeclaration(jpTypeDeclaration);
            return String.format("%s.%s", typeDeclaration.getQualifiedName(), getName());
        } else {
            com.github.javaparser.ast.body.MethodDeclaration jpMethodDeclaration = (com.github.javaparser.ast.body.MethodDeclaration)wrappedNode.getParentNode();
            MethodDeclaration methodDeclaration = new JavaParserMethodDeclaration(jpMethodDeclaration, typeSolver());
            return String.format("%s.%s", methodDeclaration.getQualifiedSignature(), getName());
        }
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
        if (wrappedNode.getTypeBound() == null) {
            return Collections.emptyList();
        }
        return wrappedNode.getTypeBound().stream().map((astB) -> toBound(astB, typeSolver)).collect(Collectors.toList());
    }

    private Bound toBound(ClassOrInterfaceType classOrInterfaceType, TypeSolver typeSolver) {
        Type type = JavaParserFacade.get(typeSolver).convertToUsage(classOrInterfaceType, classOrInterfaceType);
        Bound bound = Bound.extendsBound(type);
        return bound;
    }

    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    public Type getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(Type type) {
        throw new UnsupportedOperationException();
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
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public boolean hasDirectlyAnnotation(String canonicalName) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<TypeParameterDeclaration> getTypeParameters() {
        return Collections.emptyList();
    }

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }

	/**
	 * Returns the JavaParser node associated with this JavaParserTypeParameter.
	 *
	 * @return A visitable JavaParser node wrapped by this object.
	 */
	public com.github.javaparser.ast.TypeParameter getWrappedNode()
	{
		return wrappedNode;
	}

    @Override
    public String toString() {
        return "JPTypeParameter(" + wrappedNode.getName() +", bounds=" + wrappedNode.getTypeBound()+ ")";
    }
}
