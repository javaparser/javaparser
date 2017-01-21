/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.Optional;

/**
 * @author Julio Vilmar Gesser
 */
public abstract class VoidVisitorAdapter<A> implements VoidVisitor<A> {

    @Override
    public void visit(final AnnotationDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getName().accept(this, arg);
        if (n.getMembers() != null) {
            for (final BodyDeclaration<?> member : n.getMembers()) {
                member.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final AnnotationMemberDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getType().accept(this, arg);
        if (n.getDefaultValue().isPresent()) {
            n.getDefaultValue().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final ArrayAccessExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        n.getIndex().accept(this, arg);
    }

    @Override
    public void visit(final ArrayCreationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getElementType().accept(this, arg);
        for (ArrayCreationLevel level : n.getLevels()) {
            level.accept(this, arg);
        }
        if (n.getInitializer().isPresent()) {
            n.getInitializer().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final ArrayInitializerExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getValues() != null) {
            for (final Expression expr : n.getValues()) {
                expr.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final AssertStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getCheck().accept(this, arg);
        if (n.getMessage().isPresent()) {
            n.getMessage().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final AssignExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getTarget().accept(this, arg);
        n.getValue().accept(this, arg);
    }

    @Override
    public void visit(final BinaryExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getLeft().accept(this, arg);
        n.getRight().accept(this, arg);
    }

    @Override
    public void visit(final BlockComment n, final A arg) {
    }

    @Override
    public void visit(final BlockStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getStatements() != null) {
            for (final Statement s : n.getStatements()) {
                s.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final BooleanLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final BreakStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getLabel().ifPresent(l -> l.accept(this, arg));
    }

    @Override
    public void visit(final CastExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
        n.getExpression().accept(this, arg);
    }

    @Override
    public void visit(final CatchClause n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getParameter().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final CharLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final ClassExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getType().accept(this, arg);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getName().accept(this, arg);
        for (final TypeParameter t : n.getTypeParameters()) {
            t.accept(this, arg);
        }
        for (final ClassOrInterfaceType c : n.getExtendedTypes()) {
            c.accept(this, arg);
        }
        for (final ClassOrInterfaceType c : n.getImplementedTypes()) {
            c.accept(this, arg);
        }
        for (final BodyDeclaration<?> member : n.getMembers()) {
            member.accept(this, arg);
        }
    }

    @Override
    public void visit(final ClassOrInterfaceType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
        }
        if (n.getTypeArguments().isPresent()) {
            for (final Type t : n.getTypeArguments().get()) {
                t.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final CompilationUnit n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getPackageDeclaration().isPresent()) {
            n.getPackageDeclaration().get().accept(this, arg);
        }
        if (n.getImports() != null) {
            for (final ImportDeclaration i : n.getImports()) {
                i.accept(this, arg);
            }
        }
        if (n.getTypes() != null) {
            for (final TypeDeclaration<?> typeDeclaration : n.getTypes()) {
                typeDeclaration.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final ConditionalExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getThenExpr().accept(this, arg);
        n.getElseExpr().accept(this, arg);
    }

    @Override
    public void visit(final ConstructorDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getTypeParameters() != null) {
            for (final TypeParameter t : n.getTypeParameters()) {
                t.accept(this, arg);
            }
        }
        n.getName().accept(this, arg);
        if (n.getParameters() != null) {
            for (final Parameter p : n.getParameters()) {
                p.accept(this, arg);
            }
        }
        if (n.getThrownExceptions() != null) {
            for (final ReferenceType name : n.getThrownExceptions()) {
                name.accept(this, arg);
            }
        }
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final ContinueStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getLabel().ifPresent(l -> l.accept(this, arg));
    }

    @Override
    public void visit(final DoStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getBody().accept(this, arg);
        n.getCondition().accept(this, arg);
    }

    @Override
    public void visit(final DoubleLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final EmptyMemberDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final EmptyStmt n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final EnclosedExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getInner().isPresent())
            n.getInner().get().accept(this, arg);
    }

    @Override
    public void visit(final EnumConstantDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getArguments() != null) {
            for (final Expression e : n.getArguments()) {
                e.accept(this, arg);
            }
        }
        if (n.getClassBody() != null) {
            for (final BodyDeclaration<?> member : n.getClassBody()) {
                member.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final EnumDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getName().accept(this, arg);
        if (n.getImplementedTypes() != null) {
            for (final ClassOrInterfaceType c : n.getImplementedTypes()) {
                c.accept(this, arg);
            }
        }
        if (n.getEntries() != null) {
            for (final EnumConstantDeclaration e : n.getEntries()) {
                e.accept(this, arg);
            }
        }
        if (n.getMembers() != null) {
            for (final BodyDeclaration<?> member : n.getMembers()) {
                member.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (!n.isThis() && n.getExpression().isPresent()) {
            n.getExpression().get().accept(this, arg);
        }
        if (n.getTypeArguments().isPresent()) {
            for (final Type t : n.getTypeArguments().get()) {
                t.accept(this, arg);
            }
        }
        if (n.getArguments() != null) {
            for (final Expression e : n.getArguments()) {
                e.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final ExpressionStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
    }

    @Override
    public void visit(final FieldAccessExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getScope().isPresent())
            n.getScope().get().accept(this, arg);
        n.getName().accept(this, arg);
    }

    @Override
    public void visit(final FieldDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        for (final VariableDeclarator var : n.getVariables()) {
            var.accept(this, arg);
        }
    }

    @Override
    public void visit(final ForeachStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getVariable().accept(this, arg);
        n.getIterable().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final ForStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getInitialization() != null) {
            for (final Expression e : n.getInitialization()) {
                e.accept(this, arg);
            }
        }
        if (n.getCompare().isPresent()) {
            n.getCompare().get().accept(this, arg);
        }
        if (n.getUpdate() != null) {
            for (final Expression e : n.getUpdate()) {
                e.accept(this, arg);
            }
        }
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final IfStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getThenStmt().accept(this, arg);
        if (n.getElseStmt().isPresent()) {
            n.getElseStmt().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final InitializerDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final InstanceOfExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
        n.getType().accept(this, arg);
    }

    @Override
    public void visit(final IntegerLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final JavadocComment n, final A arg) {
    }

    @Override
    public void visit(final LabeledStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getStatement().accept(this, arg);
    }

    @Override
    public void visit(final LineComment n, final A arg) {
    }

    @Override
    public void visit(final LongLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final MarkerAnnotationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
    }

    @Override
    public void visit(final MemberValuePair n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getValue().accept(this, arg);
    }

    @Override
    public void visit(final MethodCallExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
        }
        if (n.getTypeArguments().isPresent()) {
            for (final Type t : n.getTypeArguments().get()) {
                t.accept(this, arg);
            }
        }
        n.getName().accept(this, arg);
        if (n.getArguments() != null) {
            for (final Expression e : n.getArguments()) {
                e.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final MethodDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getTypeParameters() != null) {
            for (final TypeParameter t : n.getTypeParameters()) {
                t.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        n.getName().accept(this, arg);
        if (n.getParameters() != null) {
            for (final Parameter p : n.getParameters()) {
                p.accept(this, arg);
            }
        }
        if (n.getThrownExceptions() != null) {
            for (final ReferenceType name : n.getThrownExceptions()) {
                name.accept(this, arg);
            }
        }
        if (n.getBody().isPresent()) {
            n.getBody().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final NameExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final NormalAnnotationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        if (n.getPairs() != null) {
            for (final MemberValuePair m : n.getPairs()) {
                m.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final NullLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final ObjectCreationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getScope().isPresent()) {
            n.getScope().get().accept(this, arg);
        }
        if (n.getTypeArguments().isPresent()) {
            for (final Type t : n.getTypeArguments().get()) {
                t.accept(this, arg);
            }
        }
        n.getType().accept(this, arg);
        if (n.getArguments() != null) {
            for (final Expression e : n.getArguments()) {
                e.accept(this, arg);
            }
        }
        if (n.getAnonymousClassBody().isPresent()) {
            for (final BodyDeclaration<?> member : n.getAnonymousClassBody().get()) {
                member.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final PackageDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getName().accept(this, arg);
    }

    @Override
    public void visit(final Parameter n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getType().accept(this, arg);
        n.getName().accept(this, arg);
    }

    @Override
    public void visit(final PrimitiveType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
    }

    @Override
    public void visit(final Name n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getQualifier().isPresent()) {
            n.getQualifier().get().accept(this, arg);
        }
    }

    @Override
    public void visit(SimpleName n, A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(ArrayType n, A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        n.getComponentType().accept(this, arg);
    }

    @Override
    public void visit(ArrayCreationLevel n, A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getDimension().isPresent()) {
            n.getDimension().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final IntersectionType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        for (ReferenceType element : n.getElements()) {
            element.accept(this, arg);
        }
    }

    @Override
    public void visit(final UnionType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        for (ReferenceType element : n.getElements()) {
            element.accept(this, arg);
        }
    }

    @Override
    public void visit(final ReturnStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getExpression().isPresent()) {
            n.getExpression().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final SingleMemberAnnotationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        n.getMemberValue().accept(this, arg);
    }

    @Override
    public void visit(final StringLiteralExpr n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final SuperExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getClassExpr().isPresent()) {
            n.getClassExpr().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final SwitchEntryStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getLabel().isPresent()) {
            n.getLabel().get().accept(this, arg);
        }
        if (n.getStatements() != null) {
            for (final Statement s : n.getStatements()) {
                s.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final SwitchStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getSelector().accept(this, arg);
        if (n.getEntries() != null) {
            for (final SwitchEntryStmt e : n.getEntries()) {
                e.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final SynchronizedStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final ThisExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getClassExpr().isPresent()) {
            n.getClassExpr().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final ThrowStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
    }

    @Override
    public void visit(final TryStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getResources() != null) {
            for (final VariableDeclarationExpr v : n.getResources()) {
                v.accept(this, arg);
            }
        }
        if (n.getTryBlock().isPresent()) {
            n.getTryBlock().get().accept(this, arg);
        }
        for (final CatchClause c : n.getCatchClauses()) {
            c.accept(this, arg);
        }
        if (n.getFinallyBlock().isPresent()) {
            n.getFinallyBlock().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final LocalClassDeclarationStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getClassDeclaration().accept(this, arg);
    }

    @Override
    public void visit(final TypeParameter n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getTypeBound() != null) {
            for (final ClassOrInterfaceType c : n.getTypeBound()) {
                c.accept(this, arg);
            }
        }
    }

    @Override
    public void visit(final UnaryExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getExpression().accept(this, arg);
    }

    @Override
    public void visit(final UnknownType n, final A arg) {
        visitComment(n.getComment(), arg);
    }

    @Override
    public void visit(final VariableDeclarationExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        for (final VariableDeclarator v : n.getVariables()) {
            v.accept(this, arg);
        }
    }

    @Override
    public void visit(final VariableDeclarator n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
        n.getType().accept(this, arg);
        if (n.getInitializer().isPresent()) {
            n.getInitializer().get().accept(this, arg);
        }
    }

    @Override
    public void visit(final VoidType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);

    }

    @Override
    public void visit(final WhileStmt n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getCondition().accept(this, arg);
        n.getBody().accept(this, arg);
    }

    @Override
    public void visit(final WildcardType n, final A arg) {
        visitComment(n.getComment(), arg);
        visitAnnotations(n, arg);
        if (n.getExtendedTypes().isPresent()) {
            n.getExtendedTypes().get().accept(this, arg);
        }
        if (n.getSuperTypes().isPresent()) {
            n.getSuperTypes().get().accept(this, arg);
        }
    }

    @Override
    public void visit(LambdaExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getParameters() != null) {
            for (final Parameter a : n.getParameters()) {
                a.accept(this, arg);
            }
        }
        if (n.getBody() != null) {
            n.getBody().accept(this, arg);
        }
    }

    @Override
    public void visit(MethodReferenceExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getTypeArguments().isPresent()) {
            for (final Type t : n.getTypeArguments().get()) {
                t.accept(this, arg);
            }
        }
        if (n.getScope() != null) {
            n.getScope().accept(this, arg);
        }
    }

    @Override
    public void visit(TypeExpr n, final A arg) {
        visitComment(n.getComment(), arg);
        if (n.getType() != null) {
            n.getType().accept(this, arg);
        }
    }

    @Override
    public void visit(NodeList n, A arg) {
        for (Object node : n) {
            ((Node) node).accept(this, arg);
        }
    }

    @Override
    public void visit(final ImportDeclaration n, final A arg) {
        visitComment(n.getComment(), arg);
        n.getName().accept(this, arg);
    }
    
    private void visitComment(final Optional<Comment> n, final A arg) {
        n.ifPresent(n2 -> n2.accept(this, arg));
    }

    private void visitAnnotations(NodeWithAnnotations<?> n, A arg) {
        for (AnnotationExpr annotation : n.getAnnotations()) {
            annotation.accept(this, arg);
        }
    }
}
