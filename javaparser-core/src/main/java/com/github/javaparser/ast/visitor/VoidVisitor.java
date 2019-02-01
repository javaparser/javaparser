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

/**
 * A visitor that does not return anything.
 *
 * @author Julio Vilmar Gesser
 */
public interface VoidVisitor<A> {

    void visit(NodeList n, A arg);

    void visit(AnnotationDeclaration n, A arg);

    void visit(AnnotationMemberDeclaration n, A arg);

    void visit(ArrayAccessExpr n, A arg);

    void visit(ArrayCreationExpr n, A arg);

    void visit(ArrayCreationLevel n, A arg);

    void visit(ArrayInitializerExpr n, A arg);

    void visit(ArrayType n, A arg);

    void visit(AssertStmt n, A arg);

    void visit(AssignExpr n, A arg);

    void visit(BinaryExpr n, A arg);

    void visit(BlockComment n, A arg);

    void visit(BlockStmt n, A arg);

    void visit(BooleanLiteralExpr n, A arg);

    void visit(BreakStmt n, A arg);

    void visit(CastExpr n, A arg);

    void visit(CatchClause n, A arg);

    void visit(CharLiteralExpr n, A arg);

    void visit(ClassExpr n, A arg);

    void visit(ClassOrInterfaceDeclaration n, A arg);

    void visit(ClassOrInterfaceType n, A arg);

    void visit(CompilationUnit n, A arg);

    void visit(ConditionalExpr n, A arg);

    void visit(ConstructorDeclaration n, A arg);

    void visit(ContinueStmt n, A arg);

    void visit(DoStmt n, A arg);

    void visit(DoubleLiteralExpr n, A arg);

    void visit(EmptyStmt n, A arg);

    void visit(EnclosedExpr n, A arg);

    void visit(EnumConstantDeclaration n, A arg);

    void visit(EnumDeclaration n, A arg);

    void visit(ExplicitConstructorInvocationStmt n, A arg);

    void visit(ExpressionStmt n, A arg);

    void visit(FieldAccessExpr n, A arg);

    void visit(FieldDeclaration n, A arg);

    void visit(ForStmt n, A arg);

    void visit(ForEachStmt n, A arg);

    void visit(IfStmt n, A arg);

    void visit(ImportDeclaration n, A arg);

    void visit(InitializerDeclaration n, A arg);

    void visit(InstanceOfExpr n, A arg);

    void visit(IntegerLiteralExpr n, A arg);

    void visit(IntersectionType n, A arg);

    void visit(JavadocComment n, A arg);

    void visit(LabeledStmt n, A arg);

    void visit(LambdaExpr n, A arg);

    void visit(LineComment n, A arg);

    void visit(LocalClassDeclarationStmt n, A arg);

    void visit(LongLiteralExpr n, A arg);

    void visit(MarkerAnnotationExpr n, A arg);

    void visit(MemberValuePair n, A arg);

    void visit(MethodCallExpr n, A arg);

    void visit(MethodDeclaration n, A arg);

    void visit(MethodReferenceExpr n, A arg);

    void visit(NameExpr n, A arg);

    void visit(Name n, A arg);

    void visit(NormalAnnotationExpr n, A arg);

    void visit(NullLiteralExpr n, A arg);

    void visit(ObjectCreationExpr n, A arg);

    void visit(PackageDeclaration n, A arg);

    void visit(Parameter n, A arg);

    void visit(PrimitiveType n, A arg);

    void visit(ReturnStmt n, A arg);

    void visit(SimpleName n, A arg);

    void visit(SingleMemberAnnotationExpr n, A arg);

    void visit(StringLiteralExpr n, A arg);

    void visit(SuperExpr n, A arg);

    void visit(SwitchEntry n, A arg);

    void visit(SwitchStmt n, A arg);

    void visit(SynchronizedStmt n, A arg);

    void visit(ThisExpr n, A arg);

    void visit(ThrowStmt n, A arg);

    void visit(TryStmt n, A arg);

    void visit(TypeExpr n, A arg);

    void visit(TypeParameter n, A arg);

    void visit(UnaryExpr n, A arg);

    void visit(UnionType n, A arg);

    void visit(UnknownType n, A arg);

    void visit(VariableDeclarationExpr n, A arg);

    void visit(VariableDeclarator n, A arg);

    void visit(VoidType n, A arg);

    void visit(WhileStmt n, A arg);

    void visit(WildcardType n, A arg);

    void visit(ModuleDeclaration n, A arg);

    void visit(ModuleRequiresDirective n, A arg);

    void visit(ModuleExportsDirective n, A arg);

    void visit(ModuleProvidesDirective n, A arg);

    void visit(ModuleUsesDirective n, A arg);

    void visit(ModuleOpensDirective n, A arg);

    void visit(UnparsableStmt n, A arg);

    void visit(ReceiverParameter n, A arg);

    void visit(VarType n, A arg);

    void visit(Modifier n, A arg);

    void visit(SwitchExpr switchExpr, A arg);
}
