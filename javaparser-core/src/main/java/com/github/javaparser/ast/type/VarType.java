/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.ast.type;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.VarTypeMetaModel;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedType;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * <h1>A type called "var" waiting for Java to infer it.</h1>
 * Examples:
 * <ol>
 * <li><b>var</b> a = 1;</li>
 * <li><b>var</b> a = new ArrayList&lt;String&gt;();</li>
 * </ol>
 */
public class VarType extends Type {

    private static final String JAVA_LANG_OBJECT = Object.class.getCanonicalName();

    @AllFieldsConstructor
    public VarType() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public VarType(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public VarType setAnnotations(NodeList<AnnotationExpr> annotations) {
        return (VarType) super.setAnnotations(annotations);
    }

    @Override
    public String asString() {
        return "var";
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public VarType clone() {
        return (VarType) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public VarTypeMetaModel getMetaModel() {
        return JavaParserMetaModel.varTypeMetaModel;
    }

    @Override
    public ResolvedType resolve() {
        return getSymbolResolver().toResolvedType(this, ResolvedType.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isVarType() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public VarType asVarType() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<VarType> toVarType() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifVarType(Consumer<VarType> action) {
        action.accept(this);
    }

    @Override
    public ResolvedType convertToUsage(Context context) {
        Node parent = getParentNode().get();
        if (!(parent instanceof VariableDeclarator)) {
            throw new IllegalStateException("Trying to resolve a `var` which is not in a variable declaration.");
        }
        final VariableDeclarator variableDeclarator = (VariableDeclarator) parent;
        Optional<Expression> initializer = variableDeclarator.getInitializer();
        if (!initializer.isPresent()) {
            // When a `var` type decl has no initializer it may be part of a
            // for-each statement (e.g. `for(var i : expr)`).
            Optional<ForEachStmt> forEachStmt = forEachStmtWithVariableDeclarator(variableDeclarator);
            if (forEachStmt.isPresent()) {
                Expression iterable = forEachStmt.get().getIterable();
                ResolvedType iterType = iterable.calculateResolvedType();
                if (iterType instanceof ResolvedArrayType) {
                    // The type of a variable in a for-each loop with an array
                    // is the component type of the array.
                    return ((ResolvedArrayType) iterType).getComponentType();
                }
                if (iterType.isReferenceType()) {
                    // The type of a variable in a for-each loop with an
                    // Iterable with parameter type
                    List<ResolvedType> parametersType = iterType.asReferenceType().typeParametersMap().getTypes();
                    if (parametersType.isEmpty()) {
                        Optional<ResolvedTypeDeclaration> oObjectDeclaration = context.solveType(JAVA_LANG_OBJECT).getDeclaration();
                        return oObjectDeclaration.map(decl -> ReferenceTypeImpl.undeterminedParameters(decl.asReferenceType())).orElseThrow(() -> new UnsupportedOperationException());
                    }
                    return parametersType.get(0);
                }
            }
        }
        return initializer.map(Expression::calculateResolvedType).orElseThrow(() -> new IllegalStateException("Cannot resolve `var` which has no initializer."));
    }

    private Optional<ForEachStmt> forEachStmtWithVariableDeclarator(VariableDeclarator variableDeclarator) {
        Optional<Node> node = variableDeclarator.getParentNode();
        if (!node.isPresent() || !(node.get() instanceof VariableDeclarationExpr)) {
            return Optional.empty();
        }
        node = node.get().getParentNode();
        if (!node.isPresent() || !(node.get() instanceof ForEachStmt)) {
            return Optional.empty();
        }
        return Optional.of((ForEachStmt) node.get());
    }
}
