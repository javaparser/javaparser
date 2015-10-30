package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.TypeParameter;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

import java.util.Collections;
import java.util.List;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserTypeVariableDeclaration implements TypeDeclaration {

    private TypeParameter wrappedNode;

    public JavaParserTypeVariableDeclaration(TypeParameter wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public String getQualifiedName() {
        return getName();
    }

    @Override
    public Context getContext() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
        return "JavaParserTypeVariableDeclaration{" +
                wrappedNode.getName() +
                '}';
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    public TypeUsage getUsage(Node node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isAssignableBy(TypeUsage typeUsage, TypeSolver typeSolver) {
        if (typeUsage.isTypeVariable()) {
            throw new UnsupportedOperationException("Is this type variable declaration assignable by " + typeUsage.describe());
        } else {
            throw new UnsupportedOperationException("Is this type variable declaration assignable by " + typeUsage);
        }
    }

    @Override
    public boolean isTypeVariable() {
        return true;
    }

    @Override
    public FieldDeclaration getField(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean hasField(String name, TypeSolver typeSolver) {
        return false;
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver) {
        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<ReferenceTypeUsage> getAllAncestors(TypeSolver typeSolver) {
        throw new UnsupportedOperationException();
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
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return true;
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
    public List<me.tomassetti.symbolsolver.resolution.TypeParameter> getTypeParameters() {
        return Collections.emptyList();
    }

    public me.tomassetti.symbolsolver.resolution.TypeParameter asTypeParameter() {
        return new JavaParserTypeParameter(this.wrappedNode);
    }
}
