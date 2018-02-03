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
 * A visitor that has a return value.
 *
 * @author Julio Vilmar Gesser
 */
public interface GenericVisitor<R, A> {

    // - Compilation Unit ----------------------------------
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(CompilationUnit n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(PackageDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(TypeParameter n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(LineComment n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(BlockComment n, A arg);

    // - Body ----------------------------------------------
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ClassOrInterfaceDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(EnumDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(EnumConstantDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(AnnotationDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(AnnotationMemberDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(FieldDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(VariableDeclarator n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ConstructorDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(MethodDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(Parameter n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(InitializerDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(JavadocComment n, A arg);

    // - Type ----------------------------------------------
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ClassOrInterfaceType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(PrimitiveType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ArrayType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ArrayCreationLevel n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(IntersectionType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(UnionType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(VoidType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(WildcardType n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(UnknownType n, A arg);

    // - Expression ----------------------------------------
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ArrayAccessExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ArrayCreationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ArrayInitializerExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(AssignExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(BinaryExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(CastExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ClassExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ConditionalExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(EnclosedExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(FieldAccessExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(InstanceOfExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(StringLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(IntegerLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(LongLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(CharLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(DoubleLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(BooleanLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(NullLiteralExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(MethodCallExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(NameExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ObjectCreationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ThisExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SuperExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(UnaryExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(VariableDeclarationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(MarkerAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SingleMemberAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(NormalAnnotationExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(MemberValuePair n, A arg);

    // - Statements ----------------------------------------
    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ExplicitConstructorInvocationStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(LocalClassDeclarationStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(AssertStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(BlockStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(LabeledStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(EmptyStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ExpressionStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SwitchStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SwitchEntryStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(BreakStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ReturnStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(IfStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(WhileStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ContinueStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(DoStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ForeachStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ForStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ThrowStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SynchronizedStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(TryStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(CatchClause n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(LambdaExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(MethodReferenceExpr n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(TypeExpr n, A arg);

    R visit(NodeList n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(Name n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(SimpleName n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ImportDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleDeclaration n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleRequiresStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleExportsStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleProvidesStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleUsesStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ModuleOpensStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(UnparsableStmt n, A arg);

    @Generated("com.github.javaparser.generator.core.visitor.GenericVisitorGenerator")
    R visit(ReceiverParameter n, A arg);

    R visit(VarType n, A arg);
}
