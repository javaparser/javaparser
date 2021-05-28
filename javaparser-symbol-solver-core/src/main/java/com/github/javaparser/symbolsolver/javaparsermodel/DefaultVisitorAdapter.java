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

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.jml.body.*;
import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.locref.*;
import com.github.javaparser.ast.jml.stmt.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
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
    public ResolvedType visit(JmlQuantifiedExpr n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(AccessibleClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlClauseHL n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlClauseLE n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ContinuesClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(DivergesClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(EnsuresClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlStmtWithExpression n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlLabel n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlLetExpr n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlMultiCompareExpr n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlSetStmt n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LoopDecreasesClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LoopInvariantClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LoopVariantClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlClauseE n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ModifiesClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlClauseHE n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ReturnsClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SignalsClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(SignalsOnlyClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlUnreachableStmt n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CallableClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(CapturesClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(DurationClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ForallClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlFunction n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }


    @Override
    public ResolvedType visit(JmlName n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlRefiningStmt n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(OldClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(WhenClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(WorkingSpaceClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlBoundVariable n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(ClassInvariantClause n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlClassAccessibleDeclaration n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlRepresentsDeclaration n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlContract n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlBodyDeclaration n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlContracts n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlStatements n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetArrayAccess n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetBindingExpr n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetFieldAccess n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetFunction n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetConstructorExpression n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetPrimary n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlSetComprehension n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlGhostStatements n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(JmlMethodDeclaration n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetWrapperExpression n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
    }

    @Override
    public ResolvedType visit(LocationSetStoreRef n, Boolean arg) {
        throw new UnsupportedOperationException(n.getClass().getCanonicalName());
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
