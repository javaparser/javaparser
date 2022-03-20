/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;
import static java.util.Collections.singletonList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
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
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserPatternDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractJavaParserContext<N extends Node> implements Context {

    protected N wrappedNode;
    protected TypeSolver typeSolver;

    ///
    /// Static methods
    ///
    
    protected static boolean isQualifiedName(String name) {
        return name.contains(".");
    }

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
        return wrappedNode == null ? 0 : wrappedNode.hashCode();
    }

    @Override
    public final Optional<Context> getParent() {
        Node parentNode = wrappedNode.getParentNode().orElse(null);

        // TODO/FiXME: Document why the method call expression is treated differently.
        if (parentNode instanceof MethodCallExpr) {
            MethodCallExpr parentCall = (MethodCallExpr) parentNode;
            // TODO: Can this be replaced with: boolean found = parentCall.getArguments().contains(wrappedNode);
            boolean found = false;
            for (Expression expression : parentCall.getArguments()) {
                if (expression == wrappedNode) {
                    found = true;
                    break;
                }
            }
            if (found) {
                Node notMethod = parentNode;
                while (notMethod instanceof MethodCallExpr) {
                    notMethod = demandParentNode(notMethod);
                }
                return Optional.of(JavaParserFactory.getContext(notMethod, typeSolver));
            }
        }
        Node notMethodNode = parentNode;
        // to avoid an infinite loop if parent scope is the same as wrapped node 
        while (notMethodNode instanceof MethodCallExpr || notMethodNode instanceof FieldAccessExpr
                || (notMethodNode != null && notMethodNode.hasScope() && getScope(notMethodNode).equals(wrappedNode)) ) {
            notMethodNode = notMethodNode.getParentNode().orElse(null);
        }
        if (notMethodNode == null) {
            return Optional.empty();
        }
        Context parentContext = JavaParserFactory.getContext(notMethodNode, typeSolver);
        return Optional.of(parentContext);
    }
    
    // before to call this method verify the node has a scope 
    protected Node getScope(Node node) {
        return (Node) ((NodeWithOptionalScope)node).getScope().get();
    }


    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInParentContext(String name) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved(ResolvedValueDeclaration.class);
        }

        // First check if there are any pattern expressions available to this node.
        Context parentContext = optionalParentContext.get();
        if(parentContext instanceof BinaryExprContext || parentContext instanceof IfStatementContext) {
            List<PatternExpr> patternExprs = parentContext.patternExprsExposedToChild(this.getWrappedNode());

            Optional<PatternExpr> localResolutionResults = patternExprs
                    .stream()
                    .filter(vd -> vd.getNameAsString().equals(name))
                    .findFirst();

            if (localResolutionResults.isPresent()) {
                if(patternExprs.size() == 1) {
                    JavaParserPatternDeclaration decl = JavaParserSymbolDeclaration.patternVar(localResolutionResults.get(), typeSolver);
                    return SymbolReference.solved(decl);
                } else if(patternExprs.size() > 1) {
                    throw new IllegalStateException("Unexpectedly more than one reference in scope");
                }
            }
        }

        // Delegate solving to the parent context.
        return parentContext.solveSymbol(name);
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
                    // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
                    return singletonList(
                            typeOfScope.asWildcard()
                                    .getBoundedType()
                                    .asReferenceType()
                                    .getTypeDeclaration()
                                    .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
                    );
                } else {
                    return singletonList(new ReflectionClassDeclaration(Object.class, typeSolver).asReferenceType());
                }
            } else if (typeOfScope.isArray()) {
                // method call on array are Object methods
                return singletonList(new ReflectionClassDeclaration(Object.class, typeSolver).asReferenceType());
            } else if (typeOfScope.isTypeVariable()) {
                Collection<ResolvedReferenceTypeDeclaration> result = new ArrayList<>();
                for (ResolvedTypeParameterDeclaration.Bound bound : typeOfScope.asTypeParameter().getBounds()) {
                    // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
                    result.add(
                            bound.getType()
                                    .asReferenceType()
                                    .getTypeDeclaration()
                                    .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
                    );
                }
                return result;
            } else if (typeOfScope.isConstraint()) {
                // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
                return singletonList(
                        typeOfScope.asConstraintType()
                                .getBound()
                                .asReferenceType()
                                .getTypeDeclaration()
                                .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
                );
            } else if (typeOfScope.isUnionType()) {
                return typeOfScope.asUnionType().getCommonAncestor()
                        .flatMap(ResolvedReferenceType::getTypeDeclaration)
                        .map(Collections::singletonList)
                        .orElseThrow(() -> new UnsolvedSymbolException("No common ancestor available for UnionType" + typeOfScope.describe()));
            }

            // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
            return singletonList(
                    typeOfScope.asReferenceType()
                            .getTypeDeclaration()
                            .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
            );
        }

        ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);

        // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
        return singletonList(
                typeOfScope.asReferenceType()
                        .getTypeDeclaration()
                        .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty."))
        );
    }

    public N getWrappedNode() {
        return wrappedNode;
    }
}
