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
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import javax.annotation.Generated;

/**
 * A visitor that does not return anything.
 *
 * @author Julio Vilmar Gesser
 */
public interface VoidVisitor<A> {

    void visit(NodeList n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(AnnotationDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(AnnotationMemberDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ArrayAccessExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ArrayCreationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ArrayCreationLevel n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ArrayInitializerExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ArrayType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(AssertStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(AssignExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(BinaryExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(BlockComment n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(BlockStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(BooleanLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(BreakStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(CastExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(CatchClause n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(CharLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ClassExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ClassOrInterfaceDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ClassOrInterfaceType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(CompilationUnit n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ConditionalExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ConstructorDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ContinueStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(DoStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(DoubleLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(EmptyStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(EnclosedExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(EnumConstantDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(EnumDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ExplicitConstructorInvocationStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ExpressionStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(FieldAccessExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(FieldDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ForStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ForeachStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(IfStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ImportDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(InitializerDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(InstanceOfExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(IntegerLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(IntersectionType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(JavadocComment n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(LabeledStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(LambdaExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(LineComment n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(LocalClassDeclarationStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(LongLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(MarkerAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(MemberValuePair n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(MethodCallExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(MethodDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(MethodReferenceExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(NameExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(Name n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(NormalAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(NullLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ObjectCreationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(PackageDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(Parameter n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(PrimitiveType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ReturnStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SimpleName n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SingleMemberAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(StringLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SuperExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SwitchEntryStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SwitchStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(SynchronizedStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ThisExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ThrowStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(TryStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(TypeExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(TypeParameter n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(UnaryExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(UnionType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(UnknownType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(VariableDeclarationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(VariableDeclarator n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(VoidType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(WhileStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(WildcardType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleRequiresStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleExportsStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleProvidesStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleUsesStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ModuleOpensStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(UnparsableStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.VoidVisitorGenerator")
    void visit(ReceiverParameter n, A arg);

    void visit(VarType n, A arg);
}
