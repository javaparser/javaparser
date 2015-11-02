package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import me.tomassetti.symbolsolver.logic.AbstractTypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class JavaParserTypeParameter extends AbstractTypeDeclaration implements TypeParameter {

    private com.github.javaparser.ast.TypeParameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserTypeParameter(com.github.javaparser.ast.TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
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
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeUsage(other, typeSolver));
    }

    @Override
    public String getName() {
        return wrappedNode.getName();
    }

    @Override
    public boolean declaredOnClass() {
        return (wrappedNode.getParentNode() instanceof ClassOrInterfaceDeclaration);
    }

    @Override
    public boolean declaredOnMethod() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getQNameOfDeclaringClass() {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Bound> getBounds(TypeSolver typeSolver) {
        if (wrappedNode.getTypeBound() == null) {
            return Collections.emptyList();
        }
        return wrappedNode.getTypeBound().stream().map((astB) -> toBound(astB, typeSolver)).collect(Collectors.toList());
    }

    private Bound toBound(ClassOrInterfaceType classOrInterfaceType, TypeSolver typeSolver) {
        TypeUsage typeUsage = JavaParserFacade.get(typeSolver).convertToUsage(classOrInterfaceType, classOrInterfaceType);
        Bound bound = Bound.extendsBound(typeUsage);
        return bound;
    }

    @Override
    public String getQualifiedName() {
        return getName();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    public TypeUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage) {
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
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public List<TypeParameter> getTypeParameters() {
        return Collections.emptyList();
    }

    @Override
    protected TypeSolver typeSolver() {
        return typeSolver;
    }
}
