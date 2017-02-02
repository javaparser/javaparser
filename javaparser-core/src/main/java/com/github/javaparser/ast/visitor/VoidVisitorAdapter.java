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
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

/**
 * A visitor that returns nothing, and has a default implementation for all its visit
 * methods that simply visit their children in an unspecified order.
 * 
 * @author Julio Vilmar Gesser
 */
public abstract class VoidVisitorAdapter<A> implements VoidVisitor<A> {

    @Override
    public void visit(AnnotationDeclaration n, A arg) {
        n.getMembers().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(AnnotationMemberDeclaration n, A arg) {
        n.getDefaultValue().ifPresent( l -> l.accept(this, arg));
        n.getName().accept(this, arg);
        n.getType().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ArrayAccessExpr n, A arg) {
        n.getIndex().accept(this, arg);
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ArrayCreationExpr n, A arg) {
        n.getElementType().accept(this, arg);
        n.getInitializer().ifPresent( l -> l.accept(this, arg));
        n.getLevels().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ArrayInitializerExpr n, A arg) {
        n.getValues().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(AssertStmt n, A arg) {
        n.getCheck().accept(this, arg);
        n.getMessage().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(AssignExpr n, A arg) {
        n.getTarget().accept(this, arg);
        n.getValue().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(BinaryExpr n, A arg) {
        n.getLeft().accept(this, arg);
        n.getRight().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(BlockComment n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(BlockStmt n, A arg) {
        n.getStatements().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(BooleanLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(BreakStmt n, A arg) {
        n.getLabel().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(CastExpr n, A arg) {
        n.getExpression().accept(this, arg);
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(CatchClause n, A arg) {
        n.getBody().accept(this, arg);
        n.getParameter().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(CharLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ClassExpr n, A arg) {
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ClassOrInterfaceDeclaration n, A arg) {
        n.getExtendedTypes().forEach( p -> p.accept(this, arg));
        n.getImplementedTypes().forEach( p -> p.accept(this, arg));
        n.getTypeParameters().forEach( p -> p.accept(this, arg));
        n.getMembers().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ClassOrInterfaceType n, A arg) {
        n.getName().accept(this, arg);
        n.getScope().ifPresent( l -> l.accept(this, arg));
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(CompilationUnit n, A arg) {
        n.getImports().forEach( p -> p.accept(this, arg));
        n.getPackageDeclaration().ifPresent( l -> l.accept(this, arg));
        n.getTypes().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ConditionalExpr n, A arg) {
        n.getCondition().accept(this, arg);
        n.getElseExpr().accept(this, arg);
        n.getThenExpr().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ConstructorDeclaration n, A arg) {
        n.getBody().accept(this, arg);
        n.getName().accept(this, arg);
        n.getParameters().forEach( p -> p.accept(this, arg));
        n.getThrownExceptions().forEach( p -> p.accept(this, arg));
        n.getTypeParameters().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ContinueStmt n, A arg) {
        n.getLabel().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(DoStmt n, A arg) {
        n.getBody().accept(this, arg);
        n.getCondition().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(DoubleLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(EmptyMemberDeclaration n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(EmptyStmt n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(EnclosedExpr n, A arg) {
        n.getInner().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(EnumConstantDeclaration n, A arg) {
        n.getArguments().forEach( p -> p.accept(this, arg));
        n.getClassBody().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(EnumDeclaration n, A arg) {
        n.getEntries().forEach( p -> p.accept(this, arg));
        n.getImplementedTypes().forEach( p -> p.accept(this, arg));
        n.getMembers().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ExplicitConstructorInvocationStmt n, A arg) {
        n.getArguments().forEach( p -> p.accept(this, arg));
        n.getExpression().ifPresent( l -> l.accept(this, arg));
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ExpressionStmt n, A arg) {
        n.getExpression().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(FieldAccessExpr n, A arg) {
        n.getName().accept(this, arg);
        n.getScope().ifPresent( l -> l.accept(this, arg));
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(FieldDeclaration n, A arg) {
        n.getVariables().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ForeachStmt n, A arg) {
        n.getBody().accept(this, arg);
        n.getIterable().accept(this, arg);
        n.getVariable().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ForStmt n, A arg) {
        n.getBody().accept(this, arg);
        n.getCompare().ifPresent( l -> l.accept(this, arg));
        n.getInitialization().forEach( p -> p.accept(this, arg));
        n.getUpdate().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(IfStmt n, A arg) {
        n.getCondition().accept(this, arg);
        n.getElseStmt().ifPresent( l -> l.accept(this, arg));
        n.getThenStmt().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(InitializerDeclaration n, A arg) {
        n.getBody().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(InstanceOfExpr n, A arg) {
        n.getExpression().accept(this, arg);
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(IntegerLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(JavadocComment n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(LabeledStmt n, A arg) {
        n.getLabel().accept(this, arg);
        n.getStatement().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(LineComment n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(LongLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(MarkerAnnotationExpr n, A arg) {
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(MemberValuePair n, A arg) {
        n.getName().accept(this, arg);
        n.getValue().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(MethodCallExpr n, A arg) {
        n.getArguments().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getScope().ifPresent( l -> l.accept(this, arg));
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(MethodDeclaration n, A arg) {
        n.getBody().ifPresent( l -> l.accept(this, arg));
        n.getName().accept(this, arg);
        n.getParameters().forEach( p -> p.accept(this, arg));
        n.getThrownExceptions().forEach( p -> p.accept(this, arg));
        n.getType().accept(this, arg);
        n.getTypeParameters().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(NameExpr n, A arg) {
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(NormalAnnotationExpr n, A arg) {
        n.getPairs().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(NullLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ObjectCreationExpr n, A arg) {
        n.getAnonymousClassBody().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getArguments().forEach( p -> p.accept(this, arg));
        n.getScope().ifPresent( l -> l.accept(this, arg));
        n.getType().accept(this, arg);
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(PackageDeclaration n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(Parameter n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getName().accept(this, arg);
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(PrimitiveType n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(Name n, A arg) {
        n.getQualifier().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SimpleName n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ArrayType n, A arg) {
        n.getComponentType().accept(this, arg);
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ArrayCreationLevel n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getDimension().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(IntersectionType n, A arg) {
        n.getElements().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(UnionType n, A arg) {
        n.getElements().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ReturnStmt n, A arg) {
        n.getExpression().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SingleMemberAnnotationExpr n, A arg) {
        n.getMemberValue().accept(this, arg);
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(StringLiteralExpr n, A arg) {
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SuperExpr n, A arg) {
        n.getClassExpr().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SwitchEntryStmt n, A arg) {
        n.getLabel().ifPresent( l -> l.accept(this, arg));
        n.getStatements().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SwitchStmt n, A arg) {
        n.getEntries().forEach( p -> p.accept(this, arg));
        n.getSelector().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(SynchronizedStmt n, A arg) {
        n.getBody().accept(this, arg);
        n.getExpression().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ThisExpr n, A arg) {
        n.getClassExpr().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(ThrowStmt n, A arg) {
        n.getExpression().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(TryStmt n, A arg) {
        n.getCatchClauses().forEach( p -> p.accept(this, arg));
        n.getFinallyBlock().ifPresent( l -> l.accept(this, arg));
        n.getResources().forEach( p -> p.accept(this, arg));
        n.getTryBlock().ifPresent( l -> l.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(LocalClassDeclarationStmt n, A arg) {
        n.getClassDeclaration().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(TypeParameter n, A arg) {
        n.getName().accept(this, arg);
        n.getTypeBound().forEach( p -> p.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(UnaryExpr n, A arg) {
        n.getExpression().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(UnknownType n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(VariableDeclarationExpr n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getVariables().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(VariableDeclarator n, A arg) {
        n.getInitializer().ifPresent( l -> l.accept(this, arg));
        n.getName().accept(this, arg);
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(VoidType n, A arg) {
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(WhileStmt n, A arg) {
        n.getBody().accept(this, arg);
        n.getCondition().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(WildcardType n, A arg) {
        n.getExtendedTypes().ifPresent( l -> l.accept(this, arg));
        n.getSuperTypes().ifPresent( l -> l.accept(this, arg));
        n.getAnnotations().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(LambdaExpr n, A arg) {
        n.getBody().accept(this, arg);
        n.getParameters().forEach( p -> p.accept(this, arg));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(MethodReferenceExpr n, A arg) {
        n.getScope().accept(this, arg);
        n.getTypeArguments().ifPresent( l -> l.forEach( v -> v.accept(this, arg)));
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(TypeExpr n, A arg) {
        n.getType().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }

    @Override
    public void visit(NodeList n, A arg) {
        for (Object node : n) {
            ((Node) node).accept(this, arg);
        }
    }

    @Override
    public void visit(ImportDeclaration n, A arg) {
        n.getName().accept(this, arg);
        n.getComment().ifPresent( l -> l.accept(this, arg));
    }
}

