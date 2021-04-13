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

package com.github.javaparser.symbolsolver.javaparsermodel;

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
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.resolution.types.ResolvedType;

public class DefaultVisitorAdapter implements GenericVisitor<ResolvedType, Boolean> {
    @Override
    public ResolvedType visit(CompilationUnit node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(PackageDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(TypeParameter node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LineComment node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(BlockComment node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ClassOrInterfaceDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(EnumDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(EnumConstantDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AnnotationDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AnnotationMemberDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(FieldDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(VariableDeclarator node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ConstructorDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(MethodDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(Parameter node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(InitializerDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JavadocComment node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ClassOrInterfaceType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(PrimitiveType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ArrayType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ArrayCreationLevel node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(IntersectionType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(UnionType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(VoidType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(WildcardType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(UnknownType node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ArrayAccessExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ArrayCreationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ArrayInitializerExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AssignExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(BinaryExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CastExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ClassExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ConditionalExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(EnclosedExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(FieldAccessExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(InstanceOfExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(PatternExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(StringLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(IntegerLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LongLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CharLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(DoubleLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(BooleanLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(NullLiteralExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(MethodCallExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(NameExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ObjectCreationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ThisExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SuperExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(UnaryExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(VariableDeclarationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(MarkerAnnotationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SingleMemberAnnotationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(NormalAnnotationExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(MemberValuePair node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ExplicitConstructorInvocationStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocalClassDeclarationStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocalRecordDeclarationStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AssertStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(BlockStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LabeledStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(EmptyStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ExpressionStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SwitchStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SwitchEntry node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(BreakStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ReturnStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(IfStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(WhileStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ContinueStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(DoStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ForEachStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ForStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ThrowStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SynchronizedStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(TryStmt node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CatchClause node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LambdaExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(MethodReferenceExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(TypeExpr node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(NodeList node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(Name node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SimpleName node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ImportDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleDeclaration node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleRequiresDirective node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleExportsDirective node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleProvidesDirective node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleUsesDirective node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModuleOpensDirective node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(UnparsableStmt node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ReceiverParameter node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(VarType node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(Modifier node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SwitchExpr node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(YieldStmt node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(TextBlockLiteralExpr node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(RecordDeclaration node, Boolean arg) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CompactConstructorDeclaration node, Boolean aBoolean) {
        throw new UnsupportedOperationException(node.getClass().getCanonicalName());
    }
}
