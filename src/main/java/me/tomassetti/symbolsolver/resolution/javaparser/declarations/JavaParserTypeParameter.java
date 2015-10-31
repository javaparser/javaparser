package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserTypeParameter implements TypeParameter, TypeDeclaration {

    private com.github.javaparser.ast.TypeParameter wrappedNode;

    @Override
    public boolean isAssignableBy(TypeDeclaration other) {
        return isAssignableBy(new ReferenceTypeUsage(other, typeSolver));
    }

    private TypeSolver typeSolver;

    public JavaParserTypeParameter(com.github.javaparser.ast.TypeParameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
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
        return wrappedNode.getTypeBound().stream().map((astB)->toBound(astB, typeSolver)).collect(Collectors.toList());
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
}
