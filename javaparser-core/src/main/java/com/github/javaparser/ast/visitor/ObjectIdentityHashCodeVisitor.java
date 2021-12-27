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

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.jml.doc.JmlDoc;
import com.github.javaparser.ast.jml.JmlImportDeclaration;
import com.github.javaparser.ast.jml.body.*;
import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.*;
import com.github.javaparser.ast.comments.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.jml.doc.JmlDocDeclaration;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.jml.doc.JmlDocType;
import com.github.javaparser.ast.jml.expr.*;
import com.github.javaparser.ast.jml.stmt.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

/**
 * A visitor that calculates a deep hash code for a node by using the hash codes of all its properties,
 * and the hash codes of all its child nodes (by visiting those too.)
 */
public class ObjectIdentityHashCodeVisitor implements GenericVisitor<Integer, Void> {

    private static final ObjectIdentityHashCodeVisitor SINGLETON = new ObjectIdentityHashCodeVisitor();

    public static int hashCode(final Node node) {
        return node.accept(SINGLETON, null);
    }

    public Integer visit(final AnnotationDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AnnotationMemberDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayAccessExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayCreationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayCreationLevel n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayInitializerExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ArrayType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AssertStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final AssignExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BinaryExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BlockComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BlockStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BooleanLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final BreakStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CastExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CatchClause n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CharLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassOrInterfaceDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ClassOrInterfaceType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CompilationUnit n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ConditionalExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ConstructorDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ContinueStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final DoStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final DoubleLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EmptyStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnclosedExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnumConstantDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final EnumDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ExplicitConstructorInvocationStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ExpressionStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final FieldAccessExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final FieldDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ForStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ForEachStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IfStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ImportDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final InitializerDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final InstanceOfExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IntegerLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final IntersectionType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final JavadocComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LabeledStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LambdaExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LineComment n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LocalClassDeclarationStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final LocalRecordDeclarationStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final LongLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MarkerAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MemberValuePair n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodCallExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final MethodReferenceExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NameExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final Name n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(NodeList n, Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NormalAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final NullLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ObjectCreationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final PackageDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final Parameter n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final PrimitiveType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ReturnStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SimpleName n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SingleMemberAnnotationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final StringLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SuperExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SwitchEntry n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SwitchStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final SynchronizedStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ThisExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ThrowStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TryStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TypeExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final TypeParameter n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnaryExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnionType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final UnknownType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VariableDeclarationExpr n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VariableDeclarator n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final VoidType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final WhileStmt n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final WildcardType n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ModuleDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final ModuleRequiresDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleExportsDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleProvidesDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override()
    public Integer visit(final ModuleUsesDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final ModuleOpensDirective n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final UnparsableStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final ReceiverParameter n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final VarType n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final Modifier n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final SwitchExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final YieldStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final TextBlockLiteralExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final PatternExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlQuantifiedExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlAccessibleClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlClauseLabel n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlStmtWithExpression n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlLabelExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlLetExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlMultiCompareExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlDefaultClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlSignalsClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlSignalsOnlyClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlUnreachableStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlCallableClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlCapturesClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlForallClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlFunction n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlName n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlRefiningStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlClauseIf n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlBoundVariable n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlClassInvariantDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlClassAccessibleDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlRepresentsDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlContract n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlBodyDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlContracts n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlStatements n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlSetComprehension n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlGhostStatement n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final RecordDeclaration n, final Void arg) {
        return n.hashCode();
    }

    public Integer visit(final CompactConstructorDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlMethodDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlBinaryInfixExpr n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlDocDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlDocStmt n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlImportDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlDoc n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlDocType n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlFieldDeclaration n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlOldClause n, final Void arg) {
        return n.hashCode();
    }

    @Override
    public Integer visit(final JmlClassAxiomDeclaration n, final Void arg) {
        return n.hashCode();
    }
}
