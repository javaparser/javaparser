/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.AnnotationMemberDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.ReceiverParameter;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.ClassExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.InstanceOfExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.MemberValuePair;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.expr.SuperExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.expr.TextBlockLiteralExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.TypeExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleExportsDirective;
import com.github.javaparser.ast.modules.ModuleOpensDirective;
import com.github.javaparser.ast.modules.ModuleProvidesDirective;
import com.github.javaparser.ast.modules.ModuleRequiresDirective;
import com.github.javaparser.ast.modules.ModuleUsesDirective;
import com.github.javaparser.ast.stmt.AssertStmt;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ContinueStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.EmptyStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.stmt.LocalRecordDeclarationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.SynchronizedStmt;
import com.github.javaparser.ast.stmt.ThrowStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.stmt.UnparsableStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.stmt.YieldStmt;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.IntersectionType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.type.UnknownType;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.type.WildcardType;

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

    void visit(LocalRecordDeclarationStmt n, A arg);

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

    void visit(RecordDeclaration n, A arg);

    void visit(CompactConstructorDeclaration n, A arg);

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

    void visit(TextBlockLiteralExpr n, A arg);

    void visit(YieldStmt yieldStmt, A arg);

    void visit(PatternExpr n, A arg);
}
