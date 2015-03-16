/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.List;

/**
 * @author Didier Villevalois
 */
public abstract class VoidScanner<A> implements VoidVisitor<A> {

    public void scan(final Node node, final A arg) {
        if (node != null) {
            node.accept(this, arg);
        }
    }

    public void scan(final List<? extends Node> nodes, final A arg) {
        if (nodes != null) {
            for (final Node node : nodes) {
                scan(node, arg);
            }
        }
    }

    @Override
    public void visit(final AnnotationDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getMembers(), arg);
    }

    @Override
    public void visit(final AnnotationMemberDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getType(), arg);
        scan(n.getDefaultValue(), arg);
    }

    @Override
    public void visit(final ArrayAccessExpr n, final A arg) {
        scan(n.getName(), arg);
        scan(n.getIndex(), arg);
    }

    @Override
    public void visit(final ArrayCreationExpr n, final A arg) {
        scan(n.getType(), arg);
        if (n.getDimensions() != null)
            scan(n.getDimensions(), arg);
        else
            scan(n.getInitializer(), arg);
    }

    @Override
    public void visit(final ArrayInitializerExpr n, final A arg) {
        scan(n.getValues(), arg);
    }

    @Override
    public void visit(final AssertStmt n, final A arg) {
        scan(n.getCheck(), arg);
        scan(n.getMessage(), arg);
    }

    @Override
    public void visit(final AssignExpr n, final A arg) {
        scan(n.getTarget(), arg);
        scan(n.getValue(), arg);
    }

    @Override
    public void visit(final BinaryExpr n, final A arg) {
        scan(n.getLeft(), arg);
        scan(n.getRight(), arg);
    }

    @Override
    public void visit(final BlockStmt n, final A arg) {
        scan(n.getStmts(), arg);
    }

    @Override
    public void visit(final BooleanLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final BreakStmt n, final A arg) {
    }

    @Override
    public void visit(final CastExpr n, final A arg) {
        scan(n.getType(), arg);
        scan(n.getExpr(), arg);
    }

    @Override
    public void visit(final CatchClause n, final A arg) {
        scan(n.getExcept(), arg);
        scan(n.getCatchBlock(), arg);
    }

    @Override
    public void visit(final CharLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final ClassExpr n, final A arg) {
        scan(n.getType(), arg);
    }

    @Override
    public void visit(final ClassOrInterfaceDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getTypeParameters(), arg);
        scan(n.getExtends(), arg);
        scan(n.getImplements(), arg);
        scan(n.getMembers(), arg);
    }

    @Override
    public void visit(final ClassOrInterfaceType n, final A arg) {
        scan(n.getScope(), arg);
        scan(n.getTypeArgs(), arg);
    }

    @Override
    public void visit(final CompilationUnit n, final A arg) {
        scan(n.getPackage(), arg);
        scan(n.getImports(), arg);
        scan(n.getTypes(), arg);
    }

    @Override
    public void visit(final ConditionalExpr n, final A arg) {
        scan(n.getCondition(), arg);
        scan(n.getThenExpr(), arg);
        scan(n.getElseExpr(), arg);
    }

    @Override
    public void visit(final ConstructorDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getTypeParameters(), arg);
        scan(n.getParameters(), arg);
        scan(n.getThrows(), arg);
        scan(n.getBlock(), arg);
    }

    @Override
    public void visit(final ContinueStmt n, final A arg) {
    }

    @Override
    public void visit(final DoStmt n, final A arg) {
        scan(n.getBody(), arg);
        scan(n.getCondition(), arg);
    }

    @Override
    public void visit(final DoubleLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final EmptyMemberDeclaration n, final A arg) {
    }

    @Override
    public void visit(final EmptyStmt n, final A arg) {
    }

    @Override
    public void visit(final EmptyTypeDeclaration n, final A arg) {
    }

    @Override
    public void visit(final EnclosedExpr n, final A arg) {
        scan(n.getInner(), arg);
    }

    @Override
    public void visit(final EnumConstantDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getArgs(), arg);
        scan(n.getClassBody(), arg);
    }

    @Override
    public void visit(final EnumDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getImplements(), arg);
        scan(n.getEntries(), arg);
        scan(n.getMembers(), arg);
    }

    @Override
    public void visit(final ExplicitConstructorInvocationStmt n, final A arg) {
        if (!n.isThis()) {
            scan(n.getExpr(), arg);
        }
        scan(n.getTypeArgs(), arg);
        scan(n.getArgs(), arg);
    }

    @Override
    public void visit(final ExpressionStmt n, final A arg) {
        scan(n.getExpression(), arg);
    }

    @Override
    public void visit(final FieldAccessExpr n, final A arg) {
        scan(n.getScope(), arg);
    }

    @Override
    public void visit(final FieldDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getType(), arg);
        scan(n.getVariables(), arg);
    }

    @Override
    public void visit(final ForeachStmt n, final A arg) {
        scan(n.getVariable(), arg);
        scan(n.getIterable(), arg);
        scan(n.getBody(), arg);
    }

    @Override
    public void visit(final ForStmt n, final A arg) {
        scan(n.getInit(), arg);
        scan(n.getCompare(), arg);
        scan(n.getUpdate(), arg);
        scan(n.getBody(), arg);
    }

    @Override
    public void visit(final IfStmt n, final A arg) {
        scan(n.getCondition(), arg);
        scan(n.getThenStmt(), arg);
        scan(n.getElseStmt(), arg);
    }

    @Override
    public void visit(final ImportDeclaration n, final A arg) {
        scan(n.getName(), arg);
    }

    @Override
    public void visit(final InitializerDeclaration n, final A arg) {
        scan(n.getBlock(), arg);
    }

    @Override
    public void visit(final InstanceOfExpr n, final A arg) {
        scan(n.getExpr(), arg);
        scan(n.getType(), arg);
    }

    @Override
    public void visit(final IntegerLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final IntegerLiteralMinValueExpr n, final A arg) {
    }

    @Override
    public void visit(final LabeledStmt n, final A arg) {
        scan(n.getStmt(), arg);
    }

    @Override
    public void visit(final LongLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final LongLiteralMinValueExpr n, final A arg) {
    }

    @Override
    public void visit(final MarkerAnnotationExpr n, final A arg) {
        scan(n.getName(), arg);
    }

    @Override
    public void visit(final MemberValuePair n, final A arg) {
        scan(n.getValue(), arg);
    }

    @Override
    public void visit(final MethodCallExpr n, final A arg) {
        scan(n.getScope(), arg);
        scan(n.getTypeArgs(), arg);
        scan(n.getArgs(), arg);
    }

    @Override
    public void visit(final MethodDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getTypeParameters(), arg);
        scan(n.getType(), arg);
        scan(n.getParameters(), arg);
        scan(n.getThrows(), arg);
        scan(n.getBody(), arg);
    }

    @Override
    public void visit(final NameExpr n, final A arg) {
    }

    @Override
    public void visit(final NormalAnnotationExpr n, final A arg) {
        scan(n.getName(), arg);
        scan(n.getPairs(), arg);
    }

    @Override
    public void visit(final NullLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final ObjectCreationExpr n, final A arg) {
        scan(n.getScope(), arg);
        scan(n.getTypeArgs(), arg);
        scan(n.getType(), arg);
        scan(n.getArgs(), arg);
        scan(n.getAnonymousClassBody(), arg);
    }

    @Override
    public void visit(final PackageDeclaration n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getName(), arg);
    }

    @Override
    public void visit(final Parameter n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getType(), arg);
        scan(n.getId(), arg);
    }

    @Override
    public void visit(final MultiTypeParameter n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getTypes(), arg);
        scan(n.getId(), arg);
    }

    @Override
    public void visit(final PrimitiveType n, final A arg) {
    }

    @Override
    public void visit(final QualifiedNameExpr n, final A arg) {
        scan(n.getQualifier(), arg);
    }

    @Override
    public void visit(final ReferenceType n, final A arg) {
        scan(n.getType(), arg);
    }

    @Override
    public void visit(final ReturnStmt n, final A arg) {
        scan(n.getExpr(), arg);
    }

    @Override
    public void visit(final SingleMemberAnnotationExpr n, final A arg) {
        scan(n.getName(), arg);
        scan(n.getMemberValue(), arg);
    }

    @Override
    public void visit(final StringLiteralExpr n, final A arg) {
    }

    @Override
    public void visit(final SuperExpr n, final A arg) {
        scan(n.getClassExpr(), arg);
    }

    @Override
    public void visit(final SwitchEntryStmt n, final A arg) {
        scan(n.getLabel(), arg);
        scan(n.getStmts(), arg);
    }

    @Override
    public void visit(final SwitchStmt n, final A arg) {
        scan(n.getSelector(), arg);
        scan(n.getEntries(), arg);
    }

    @Override
    public void visit(final SynchronizedStmt n, final A arg) {
        scan(n.getExpr(), arg);
        scan(n.getBlock(), arg);
    }

    @Override
    public void visit(final ThisExpr n, final A arg) {
        scan(n.getClassExpr(), arg);
    }

    @Override
    public void visit(final ThrowStmt n, final A arg) {
        scan(n.getExpr(), arg);
    }

    @Override
    public void visit(final TryStmt n, final A arg) {
        scan(n.getResources(), arg);
        scan(n.getTryBlock(), arg);
        scan(n.getCatchs(), arg);
        scan(n.getFinallyBlock(), arg);
    }

    @Override
    public void visit(final TypeDeclarationStmt n, final A arg) {
        scan(n.getTypeDeclaration(), arg);
    }

    @Override
    public void visit(final TypeParameter n, final A arg) {
        scan(n.getTypeBound(), arg);
    }

    @Override
    public void visit(final UnaryExpr n, final A arg) {
        scan(n.getExpr(), arg);
    }

    @Override
    public void visit(final VariableDeclarationExpr n, final A arg) {
        scan(n.getAnnotations(), arg);
        scan(n.getType(), arg);
        scan(n.getVars(), arg);
    }

    @Override
    public void visit(final VariableDeclarator n, final A arg) {
        scan(n.getId(), arg);
        scan(n.getInit(), arg);
    }

    @Override
    public void visit(final VariableDeclaratorId n, final A arg) {
    }

    @Override
    public void visit(final VoidType n, final A arg) {
    }

    @Override
    public void visit(final WhileStmt n, final A arg) {
        scan(n.getCondition(), arg);
        scan(n.getBody(), arg);
    }

    @Override
    public void visit(final WildcardType n, final A arg) {
        scan(n.getExtends(), arg);
        scan(n.getSuper(), arg);
    }

    @Override
    public void visit(LambdaExpr n, final A arg) {
        scan(n.getParameters(), arg);
        scan(n.getBody(), arg);
    }

    @Override
    public void visit(MethodReferenceExpr n, final A arg) {
        scan(n.getTypeParameters(), arg);
        scan(n.getScope(), arg);
    }

    @Override
    public void visit(TypeExpr n, final A arg) {
        scan(n.getType(), arg);
    }
}
