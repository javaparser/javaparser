/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;
import static java.util.Collections.singletonList;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractJavaParserContext<N extends Node> implements Context {

    protected N wrappedNode;
    protected TypeSolver typeSolver;

    ///
    /// Static methods
    ///

    public static SymbolReference<ResolvedValueDeclaration> solveWith(SymbolDeclarator symbolDeclarator, String name) {
        for (ResolvedValueDeclaration decl : symbolDeclarator.getSymbolDeclarations()) {
            if (decl.getName().equals(name)) {
                return SymbolReference.solved(decl);
            }
        }
        return SymbolReference.unsolved(ResolvedValueDeclaration.class);
    }

    ///
    /// Constructors
    ///

    public AbstractJavaParserContext(N wrappedNode, TypeSolver typeSolver) {
        if (wrappedNode == null) {
            throw new NullPointerException();
        }
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    ///
    /// Public methods
    ///

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        AbstractJavaParserContext<?> that = (AbstractJavaParserContext<?>) o;

        return wrappedNode != null ? wrappedNode.equals(that.wrappedNode) : that.wrappedNode == null;
    }

    @Override
    public int hashCode() {
        return wrappedNode != null ? wrappedNode.hashCode() : 0;
    }

    @Override
    public Optional<ResolvedType> solveGenericType(String name) {
        Context parent = getParent();
        if (parent == null) {
            return Optional.empty();
        } else {
            return parent.solveGenericType(name);
        }
    }

    @Override
    public final Context getParent() {
        Node parent = wrappedNode.getParentNode().orElse(null);
        if (parent instanceof MethodCallExpr) {
            MethodCallExpr parentCall = (MethodCallExpr) parent;
            boolean found = false;
            if (parentCall.getArguments() != null) {
                for (Expression expression : parentCall.getArguments()) {
                    if (expression == wrappedNode) {
                        found = true;
                    }
                }
            }
            if (found) {
                Node notMethod = parent;
                while (notMethod instanceof MethodCallExpr) {
                    notMethod = requireParentNode(notMethod);
                }
                return JavaParserFactory.getContext(notMethod, typeSolver);
            }
        }
        Node notMethod = parent;
        while (notMethod instanceof MethodCallExpr || notMethod instanceof FieldAccessExpr) {
            notMethod = notMethod.getParentNode().orElse(null);
        }
        if (notMethod == null) {
            return null;
        }
        return JavaParserFactory.getContext(notMethod, typeSolver);
    }

    ///
    /// Protected methods
    ///

    protected Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name) {
        return symbolDeclarator.getSymbolDeclarations().stream()
                .filter(d -> d.getName().equals(name))
                .map(Value::from)
                .findFirst();
    }

    protected Collection<ResolvedReferenceTypeDeclaration> findTypeDeclarations(Optional<Expression> optScope) {
        if (optScope.isPresent()) {
            Expression scope = optScope.get();

            // consider static methods
            if (scope instanceof NameExpr) {
                NameExpr scopeAsName = scope.asNameExpr();
                SymbolReference<ResolvedTypeDeclaration> symbolReference = this.solveType(scopeAsName.getName().getId());
                if (symbolReference.isSolved() && symbolReference.getCorrespondingDeclaration().isType()) {
                    return singletonList(symbolReference.getCorrespondingDeclaration().asReferenceType());
                }
            }

            ResolvedType typeOfScope;
            try {
                typeOfScope = JavaParserFacade.get(typeSolver).getType(scope);
            } catch (Exception e) {
                // If the scope corresponds to a type we should treat it differently
                if (scope instanceof FieldAccessExpr) {
                    FieldAccessExpr scopeName = (FieldAccessExpr) scope;
                    if (this.solveType(scopeName.toString()).isSolved()) {
                        return Collections.emptyList();
                    }
                }
                throw new UnsolvedSymbolException(scope.toString(), wrappedNode.toString(), e);
            }
            if (typeOfScope.isWildcard()) {
                if (typeOfScope.asWildcard().isExtends() || typeOfScope.asWildcard().isSuper()) {
                    return singletonList(typeOfScope.asWildcard().getBoundedType().asReferenceType().getTypeDeclaration());
                } else {
                    return singletonList(new ReflectionClassDeclaration(Object.class, typeSolver).asReferenceType());
                }
            } else if (typeOfScope.isArray()) {
                // method call on array are Object methods
                return singletonList(new ReflectionClassDeclaration(Object.class, typeSolver).asReferenceType());
            } else if (typeOfScope.isTypeVariable()) {
                Collection<ResolvedReferenceTypeDeclaration> result = new ArrayList<>();
                for (ResolvedTypeParameterDeclaration.Bound bound : typeOfScope.asTypeParameter().getBounds()) {
                    result.add(bound.getType().asReferenceType().getTypeDeclaration());
                }
                return result;
            } else if (typeOfScope.isConstraint()) {
                return singletonList(typeOfScope.asConstraintType().getBound().asReferenceType().getTypeDeclaration());
            } else if (typeOfScope.isUnionType()) {
                return typeOfScope.asUnionType().getCommonAncestor()
                        .map(ResolvedReferenceType::getTypeDeclaration)
                        .map(Collections::singletonList)
                        .orElseThrow(() -> new UnsolvedSymbolException("No common ancestor available for UnionType"
                                + typeOfScope.describe()));
            }
            return singletonList(typeOfScope.asReferenceType().getTypeDeclaration());
        }
        ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);
        return singletonList(typeOfScope.asReferenceType().getTypeDeclaration());
    }

    public N getWrappedNode() {
        return wrappedNode;
    }
}
