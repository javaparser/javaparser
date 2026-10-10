/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import static com.github.javaparser.ast.expr.MatchAllPatternExpr.UNNAMED_PLACEHOLDER;
import static com.github.javaparser.resolution.Navigator.demandParentNode;
import static java.util.Collections.singletonList;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import com.github.javaparser.resolution.*;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.TypeVariableResolutionCapability;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.PatternVariableVisitor;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypePatternDeclaration;
import java.util.*;
import java.util.stream.Collectors;

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
        return SymbolReference.unsolved();
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

        // Resolution of the scope of the method call expression is delegated to parent
        // context.
        if (parentNode instanceof MethodCallExpr) {
            MethodCallExpr parentCall = (MethodCallExpr) parentNode;
            boolean found = parentCall.getArguments().contains(wrappedNode);
            if (found) {
                Node notMethod = parentNode;
                while (notMethod instanceof MethodCallExpr) {
                    notMethod = demandParentNode(notMethod);
                }
                return Optional.of(JavaParserFactory.getContext(notMethod, typeSolver));
            }
        }
        Node notMethodNode = parentNode;
        // To avoid loops JP must ensure that the scope of the parent context
        // is not the same as the current node.
        // For most part, this can be achieved that the scope of the nodes is different,
        // but in some cases, we may have loops of length > 1. This is the case for expressions
        // that have something like a "receiver" - field accesses, method calls and the
        // non-static inner class variant of constructor calls. We handle these by just
        // skipping all method calls, field accesses, and all constructor calls that have
        // a receiver (i.e., outer.new Inner()), as identified by hasScope.
        while (notMethodNode instanceof MethodCallExpr
                || notMethodNode instanceof FieldAccessExpr
                || (notMethodNode instanceof ObjectCreationExpr && notMethodNode.hasScope())
                || (notMethodNode != null
                        && notMethodNode.hasScope()
                        && getScope(notMethodNode).equals(wrappedNode))) {
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
        return (Node) ((NodeWithOptionalScope) node).getScope().get();
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbolInParentContext(String name) {
        Optional<Context> optionalParentContext = getParent();
        if (!optionalParentContext.isPresent()) {
            return SymbolReference.unsolved();
        }

        // First check if there are any pattern expressions available to this node.
        Context parentContext = optionalParentContext.get();
        if (parentContext instanceof BinaryExprContext
                || parentContext instanceof IfStatementContext
                || parentContext instanceof SwitchEntryContext) {
            List<TypePatternExpr> typePatternExprs =
                    parentContext.typePatternExprsExposedToChild(this.getWrappedNode());

            List<TypePatternExpr> localResolutionResults = typePatternExprs.stream()
                    .filter(vd -> vd.getNameAsString().equals(name))
                    .collect(Collectors.toList());

            switch (localResolutionResults.size()) {
                case 0:
                    // Delegate solving to the parent context.
                    return parentContext.solveSymbol(name);

                case 1:
                    TypePatternExpr typePatternExpr =
                            localResolutionResults.get(0).asTypePatternExpr();
                    JavaParserTypePatternDeclaration decl =
                            JavaParserSymbolDeclaration.patternVar(typePatternExpr, typeSolver);
                    return SymbolReference.solved(decl);

                default:
                    throw new IllegalStateException("Unexpectedly more than one reference in scope");
            }
        }

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

    /**
     * The declarations of the types a call or an access on {@code optScope} looks its members up in, without the
     * type arguments that {@link #findReceiverTypes(Optional)} keeps.
     */
    protected Collection<ResolvedReferenceTypeDeclaration> findTypeDeclarations(Optional<Expression> optScope) {
        // TODO: Figure out if it is appropriate to remove the orElseThrow() -- if so, how...
        return findReceiverTypes(optScope).stream()
                .map(receiverType -> receiverType
                        .getTypeDeclaration()
                        .orElseThrow(() -> new RuntimeException("TypeDeclaration unexpectedly empty.")))
                .collect(Collectors.toList());
    }

    /**
     * The types a call or an access on {@code optScope} looks its members up in, with the type arguments they
     * carry: several for a type variable bounded by an intersection, a single one otherwise.
     * <p>
     * The type of the scope is reduced to the type whose members it has: the bound of a wildcard, of a type
     * variable or of a lambda parameter constraint, {@code Object} for an array or an unbounded wildcard, the
     * common ancestor of a union type, and the enclosing type when there is no scope. Unlike a type declaration,
     * the result keeps the type arguments, e.g. {@code Box<String>} for a scope of type
     * {@code ? extends Box<String>}, so that overload resolution can take them into account.
     * <p>
     * Limitation: only method calls use these type arguments so far. Method references still look their methods
     * up through {@link #findTypeDeclarations(Optional)}, so that {@code box::set} remains ambiguous between
     * {@code set(T)} and {@code set(U)} on a {@code Box<A, B>}, even when only one of them suits the target
     * functional interface.
     */
    protected Collection<ResolvedReferenceType> findReceiverTypes(Optional<Expression> optScope) {
        if (optScope.isPresent()) {
            Expression scope = optScope.get();

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
                if (typeOfScope.asWildcard().isExtends()
                        || typeOfScope.asWildcard().isSuper()) {
                    return singletonList(
                            typeOfScope.asWildcard().getBoundedType().asReferenceType());
                }
                return singletonList(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
            }
            if (typeOfScope.isArray()) {
                // method call on array are Object methods
                return singletonList(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
            }
            if (typeOfScope.isTypeVariable()) {
                Collection<ResolvedReferenceType> result = new ArrayList<>();
                for (ResolvedTypeParameterDeclaration.Bound bound :
                        typeOfScope.asTypeParameter().getBounds()) {
                    result.add(bound.getType().asReferenceType());
                }
                return result;
            }
            if (typeOfScope.isConstraint()) {
                // A ResolvedLambdaConstraintType wraps the inferred bound of an implicit lambda
                // parameter, e.g. when resolving `a` in `Comparator.comparing(a -> a.getName())`.
                // We need the type declaration of the bound so that method lookups (like getName())
                // can proceed.
                ResolvedType type = typeOfScope.asConstraintType().getBound();
                if (type.isReferenceType()) {
                    // Common case: the bound is a fully-resolved reference type, e.g. `A`.
                    return singletonList(type.asReferenceType());
                }
                if (type.isTypeVariable()) {
                    // The bound is still an unresolved type variable (e.g. `T` in
                    // `Comparator.comparing` when no outer context inference was possible).
                    // The best we can do is use the type variable's explicit upper bounds;
                    // if the variable is unconstrained (declared as plain `T`), we fall back
                    // to Object, which is Java's implicit upper bound for all type parameters.
                    Collection<ResolvedReferenceType> result = new ArrayList<>();
                    for (ResolvedTypeParameterDeclaration.Bound bound :
                            type.asTypeParameter().getBounds()) {
                        result.add(bound.getType().asReferenceType());
                    }
                    if (result.isEmpty()) {
                        result.add(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
                    }
                    return result;
                }
                if (type.isWildcard() && type.asWildcard().isSuper()) {
                    // The bound is a `? super X` wildcard. This shape arises when
                    // LambdaExprContext infers the type of a lambda parameter by matching
                    // the outer call's expected parameter type against the inner static
                    // method's return type. For example:
                    //   stream.sorted(Comparator.comparing(a -> a.getName()))
                    // The inference learns that comparing's Comparator<T> must be a
                    // Comparator<? super A> (sorted's formal type), so T is registered as
                    // `? super A`. The constraint bound here is therefore `? super A`, and
                    // we need A's type declaration to look up `getName()`.
                    ResolvedType bounded = type.asWildcard().getBoundedType();
                    if (bounded.isReferenceType()) {
                        // Normal case: `? super A` where A is a concrete reference type.
                        return singletonList(bounded.asReferenceType());
                    }
                    if (bounded.isTypeVariable()) {
                        // Edge case: `? super T` where T is itself still an unresolved type
                        // variable (outer context inference did not fully concretize T).
                        // Apply the same upper-bound / Object fallback as the plain
                        // type-variable case above.
                        Collection<ResolvedReferenceType> result = new ArrayList<>();
                        for (ResolvedTypeParameterDeclaration.Bound bound :
                                bounded.asTypeParameter().getBounds()) {
                            result.add(bound.getType().asReferenceType());
                        }
                        if (result.isEmpty()) {
                            result.add(new ReferenceTypeImpl(typeSolver.getSolvedJavaLangObject()));
                        }
                        return result;
                    }
                }
                throw new UnsupportedOperationException(
                        "The type declaration cannot be found on constraint " + type.describe());
            }
            if (typeOfScope.isUnionType()) {
                return typeOfScope
                        .asUnionType()
                        .getCommonAncestor()
                        .filter(commonAncestor ->
                                commonAncestor.getTypeDeclaration().isPresent())
                        .map(Collections::singletonList)
                        .orElseThrow(() -> new UnsolvedSymbolException(
                                "No common ancestor available for UnionType" + typeOfScope.describe()));
            }

            return singletonList(typeOfScope.asReferenceType());
        }

        ResolvedType typeOfScope = JavaParserFacade.get(typeSolver).getTypeOfThisIn(wrappedNode);

        return singletonList(typeOfScope.asReferenceType());
    }

    /**
     * Similar to solveMethod but we return a MethodUsage.
     * A MethodUsage corresponds to a MethodDeclaration plus the resolved type variables.
     */
    @Override
    public Optional<MethodUsage> solveMethodAsUsage(String name, List<ResolvedType> argumentsTypes) {
        SymbolReference<ResolvedMethodDeclaration> methodSolved = solveMethod(name, argumentsTypes, false);
        if (methodSolved.isSolved()) {
            ResolvedMethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();
            if (!(methodDeclaration instanceof TypeVariableResolutionCapability)) {
                throw new UnsupportedOperationException(String.format(
                        "Resolved method declarations must implement %s.",
                        TypeVariableResolutionCapability.class.getName()));
            }

            MethodUsage methodUsage =
                    ((TypeVariableResolutionCapability) methodDeclaration).resolveTypeVariables(this, argumentsTypes);
            return Optional.of(methodUsage);
        }
        return Optional.empty();
    }

    @Override
    public N getWrappedNode() {
        return wrappedNode;
    }

    /**
     * When looking for a variable declaration in a pattern expression, there are 2 cases:
     *   1. The pattern expression is a type pattern expression (e.g. {@code Foo f}), in which case we can just compare
     *      the name of the variable we're trying to resolve with the name declared in the pattern.
     *   2. The pattern expression is a record pattern expression (e.g. {@code Foo (Bar b, Baz (...) )}), in which case
     *      we need to traverse the "pattern tree" to find all type pattern expressions, so that we can compare names
     *      for all of these.
     *
     * In both cases, we only really care about the type pattern expressions, so this method simply does a traversal
     * of the pattern tree to find all type pattern expressions contained in it.
     *
     * @param patternExpr the root of the pattern tree to traverse
     * @return all type pattern expressions discovered in the tree
     */
    public List<TypePatternExpr> typePatternExprsDiscoveredInPattern(ComponentPatternExpr patternExpr) {
        List<TypePatternExpr> discoveredTypePatterns = new ArrayList<>();
        Queue<ComponentPatternExpr> patternsToCheck = new ArrayDeque<>();
        patternsToCheck.add(patternExpr);

        while (!patternsToCheck.isEmpty()) {
            ComponentPatternExpr patternToCheck = patternsToCheck.remove();

            if (patternToCheck.isTypePatternExpr()) {
                if (!patternToCheck.asTypePatternExpr().getNameAsString().equals(UNNAMED_PLACEHOLDER)) {
                    discoveredTypePatterns.add(patternToCheck.asTypePatternExpr());
                }
            } else if (patternToCheck.isRecordPatternExpr()) {
                patternsToCheck.addAll(patternToCheck.asRecordPatternExpr().getPatternList());
            } else if (!patternToCheck.isMatchAllPatternExpr()) {
                throw new UnsupportedOperationException(String.format(
                        "Discovering type pattern expressions in %s not supported",
                        patternExpr.getClass().getName()));
            }
        }

        return discoveredTypePatterns;
    }

    public SymbolReference<? extends ResolvedValueDeclaration> findExposedPatternInParentContext(
            Node parent, String name) {
        Context context = JavaParserFactory.getContext(parent, typeSolver);
        List<TypePatternExpr> patternVariablesExposedToWrappedNode =
                context.typePatternExprsExposedToChild(wrappedNode);
        for (TypePatternExpr typePatternExpr : patternVariablesExposedToWrappedNode) {
            if (typePatternExpr.getNameAsString().equals(name)) {
                return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(typePatternExpr, typeSolver));
            }
        }
        return SymbolReference.unsolved();
    }

    @Override
    public List<TypePatternExpr> typePatternExprsExposedFromChildren() {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        return wrappedNode.accept(variableVisitor, null).getVariablesIntroducedIfTrue();
    }

    @Override
    public List<TypePatternExpr> negatedTypePatternExprsExposedFromChildren() {
        PatternVariableVisitor variableVisitor = new PatternVariableVisitor();
        return wrappedNode.accept(variableVisitor, null).getVariablesIntroducedIfFalse();
    }
}
