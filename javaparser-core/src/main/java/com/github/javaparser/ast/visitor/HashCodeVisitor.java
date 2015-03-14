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
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public class HashCodeVisitor implements GenericVisitor<Integer, Void> {

    private static final HashCodeVisitor SINGLETON = new HashCodeVisitor();

    private final static int PRIME = 31;

    public static int hashCode(final Node n) {
        return SINGLETON.nodeHashCode(n);
    }

    private HashCodeVisitor() {
        // hide constructor
    }

    private int nodesHashCode(final List<? extends Node> nodes) {
        int result = 1;
        for (Node node : nodes) {
            result = PRIME * result + nodeHashCode(node);
        }
        return result;
    }

    private int nodeHashCode(final Node n) {
        int result = 1;
        result = PRIME * result + (n.getCommentAttributes() == null ? 0 : commentsHashCode(n.getCommentAttributes()));
        result = PRIME * result + n.accept(this, null);
        return result;
    }

    private int commentsHashCode(final CommentAttributes comments) {
        int result = 1;
        result = PRIME * result + (comments.getLeadingComments() == null ? 0 : commentsHashCode(comments.getLeadingComments()));
        result = PRIME * result + (comments.getDanglingComments() == null ? 0 : commentsHashCode(comments.getDanglingComments()));
        result = PRIME * result + (comments.getTrailingComment() == null ? 0 : commentHashCode(comments.getTrailingComment()));
        return result;
    }

    private int commentsHashCode(List<Comment> comments) {
        int result = 1;
        for (Comment comment : comments) {
            result = PRIME * result + commentHashCode(comment);
        }
        return result;
    }

    private int commentHashCode(final Comment comment) {
        int result = 1;
        result = PRIME * result + (comment.getCommentKind() == null ? 0 : comment.getCommentKind().hashCode());
        result = PRIME * result + (comment.image() == null ? 0 : comment.image().hashCode());
        return result;
    }

    @Override
    public Integer visit(final CompilationUnit n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getPackage() == null ? 0 : nodeHashCode(n.getPackage()));
        result = PRIME * result + (n.getImports() == null ? 0 : nodesHashCode(n.getImports()));
        result = PRIME * result + (n.getTypes() == null ? 0 : nodesHashCode(n.getTypes()));
        return result;
    }

    @Override
    public Integer visit(final PackageDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final ImportDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        return result;
    }

    @Override
    public Integer visit(final TypeParameter n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getTypeBound() == null ? 0 : nodesHashCode(n.getTypeBound()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final ClassOrInterfaceDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.isInterface() ? 1231 : 1237);
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getTypeParameters() == null ? 0 : nodesHashCode(n.getTypeParameters()));
        result = PRIME * result + (n.getExtends() == null ? 0 : nodesHashCode(n.getExtends()));
        result = PRIME * result + (n.getImplements() == null ? 0 : nodesHashCode(n.getImplements()));
        result = PRIME * result + (n.getMembers() == null ? 0 : nodesHashCode(n.getMembers()));
        return result;
    }

    @Override
    public Integer visit(final EnumDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getImplements() == null ? 0 : nodesHashCode(n.getImplements()));
        result = PRIME * result + (n.getEntries() == null ? 0 : nodesHashCode(n.getEntries()));
        result = PRIME * result + (n.getMembers() == null ? 0 : nodesHashCode(n.getMembers()));
        return result;
    }

    @Override
    public Integer visit(final EmptyTypeDeclaration n, final Void arg) {
        return 1;
    }

    @Override
    public Integer visit(final EnumConstantDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getArgs() == null ? 0 : nodesHashCode(n.getArgs()));
        result = PRIME * result + (n.getClassBody() == null ? 0 : nodesHashCode(n.getClassBody()));
        return result;
    }

    @Override
    public Integer visit(final AnnotationDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getMembers() == null ? 0 : nodesHashCode(n.getMembers()));
        return result;
    }

    @Override
    public Integer visit(final AnnotationMemberDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getDefaultValue() == null ? 0 : nodeHashCode(n.getDefaultValue()));
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        return result;
    }

    @Override
    public Integer visit(final FieldDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getVariables() == null ? 0 : nodesHashCode(n.getVariables()));
        return result;
    }

    @Override
    public Integer visit(final VariableDeclarator n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getId() == null ? 0 : nodeHashCode(n.getId()));
        result = PRIME * result + (n.getInit() == null ? 0 : nodeHashCode(n.getInit()));
        return result;
    }

    @Override
    public Integer visit(final VariableDeclaratorId n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getArrayCount();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        return result;
    }

    @Override
    public Integer visit(final ConstructorDeclaration n, final Void arg) {
        int result = 1;
        // javadoc are checked at CompilationUnit

        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getBlock() == null ? 0 : nodeHashCode(n.getBlock()));
        result = PRIME * result + (n.getParameters() == null ? 0 : nodesHashCode(n.getParameters()));
        result = PRIME * result + (n.getThrows() == null ? 0 : nodesHashCode(n.getThrows()));
        result = PRIME * result + (n.getTypeParameters() == null ? 0 : nodesHashCode(n.getTypeParameters()));
        return result;
    }

    @Override
    public Integer visit(final MethodDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + n.getArrayCount();
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        result = PRIME * result + (n.getParameters() == null ? 0 : nodesHashCode(n.getParameters()));
        result = PRIME * result + (n.getThrows() == null ? 0 : nodesHashCode(n.getThrows()));
        result = PRIME * result + (n.getTypeParameters() == null ? 0 : nodesHashCode(n.getTypeParameters()));
        return result;
    }

    @Override
    public Integer visit(final Parameter n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + visit((BaseParameter) n, arg);
        return result;
    }

    @Override
    public Integer visit(final MultiTypeParameter n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getTypes() == null ? 0 : nodesHashCode(n.getTypes()));
        result = PRIME * result + visit((BaseParameter) n, arg);
        return result;
    }

    protected int visit(final BaseParameter n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getId() == null ? 0 : nodeHashCode(n.getId()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final EmptyMemberDeclaration n, final Void arg) {
        return 1;
    }

    @Override
    public Integer visit(final InitializerDeclaration n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getBlock() == null ? 0 : nodeHashCode(n.getBlock()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final ClassOrInterfaceType n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getScope() == null ? 0 : nodeHashCode(n.getScope()));
        result = PRIME * result + (n.getTypeArgs() == null ? 0 : nodesHashCode(n.getTypeArgs()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final PrimitiveType n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getType() == null ? 0 : n.getType().hashCode());
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final ReferenceType n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getArrayCount();
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        for (List<AnnotationExpr> annotationExprs : n.getArraysAnnotations()) {
            result = PRIME * result + nodesHashCode(annotationExprs);
        }
        return result;
    }

    public Integer visit(final VoidType n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final WildcardType n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExtends() == null ? 0 : nodeHashCode(n.getExtends()));
        result = PRIME * result + (n.getSuper() == null ? 0 : nodeHashCode(n.getSuper()));
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        return result;
    }

    @Override
    public Integer visit(final ArrayAccessExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        result = PRIME * result + (n.getIndex() == null ? 0 : nodeHashCode(n.getIndex()));
        return result;
    }

    @Override
    public Integer visit(final ArrayCreationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getArrayCount();
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getInitializer() == null ? 0 : nodeHashCode(n.getInitializer()));
        result = PRIME * result + (n.getDimensions() == null ? 0 : nodesHashCode(n.getDimensions()));
        for (List<AnnotationExpr> annotationExprs : n.getArraysAnnotations()) {
            result = PRIME * result + nodesHashCode(annotationExprs);
        }
        return result;
    }

    @Override
    public Integer visit(final ArrayInitializerExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValues() == null ? 0 : nodesHashCode(n.getValues()));
        return result;
    }

    @Override
    public Integer visit(final AssignExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getOperator() == null ? 0 : n.getOperator().hashCode());
        result = PRIME * result + (n.getTarget() == null ? 0 : nodeHashCode(n.getTarget()));
        result = PRIME * result + (n.getValue() == null ? 0 : nodeHashCode(n.getValue()));
        return result;
    }

    @Override
    public Integer visit(final BinaryExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getOperator() == null ? 0 : n.getOperator().hashCode());
        result = PRIME * result + (n.getLeft() == null ? 0 : nodeHashCode(n.getLeft()));
        result = PRIME * result + (n.getRight() == null ? 0 : nodeHashCode(n.getRight()));
        return result;
    }

    @Override
    public Integer visit(final CastExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        return result;
    }

    @Override
    public Integer visit(final ClassExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        return result;
    }

    @Override
    public Integer visit(final ConditionalExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getCondition() == null ? 0 : nodeHashCode(n.getCondition()));
        result = PRIME * result + (n.getThenExpr() == null ? 0 : nodeHashCode(n.getThenExpr()));
        result = PRIME * result + (n.getElseExpr() == null ? 0 : nodeHashCode(n.getElseExpr()));
        return result;
    }

    @Override
    public Integer visit(final EnclosedExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getInner() == null ? 0 : nodeHashCode(n.getInner()));
        return result;
    }

    @Override
    public Integer visit(final FieldAccessExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getScope() == null ? 0 : nodeHashCode(n.getScope()));
        result = PRIME * result + (n.getField() == null ? 0 : n.getField().hashCode());
        result = PRIME * result + (n.getTypeArgs() == null ? 0 : nodesHashCode(n.getTypeArgs()));
        return result;
    }

    @Override
    public Integer visit(final InstanceOfExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        return result;
    }

    @Override
    public Integer visit(final StringLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final IntegerLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final LongLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final IntegerLiteralMinValueExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final LongLiteralMinValueExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final CharLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final DoubleLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() == null ? 0 : n.getValue().hashCode());
        return result;
    }

    @Override
    public Integer visit(final BooleanLiteralExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getValue() ? 1231 : 1237);
        return result;
    }

    @Override
    public Integer visit(final NullLiteralExpr n, final Void arg) {
        return 1;
    }

    @Override
    public Integer visit(final MethodCallExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getScope() == null ? 0 : nodeHashCode(n.getScope()));
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getArgs() == null ? 0 : nodesHashCode(n.getArgs()));
        result = PRIME * result + (n.getTypeArgs() == null ? 0 : nodesHashCode(n.getTypeArgs()));
        return result;
    }

    @Override
    public Integer visit(final NameExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        return result;
    }

    @Override
    public Integer visit(final ObjectCreationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getScope() == null ? 0 : nodeHashCode(n.getScope()));
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getAnonymousClassBody() == null ? 0 : nodesHashCode(n.getAnonymousClassBody()));
        result = PRIME * result + (n.getArgs() == null ? 0 : nodesHashCode(n.getArgs()));
        result = PRIME * result + (n.getTypeArgs() == null ? 0 : nodesHashCode(n.getTypeArgs()));
        return result;
    }

    @Override
    public Integer visit(final QualifiedNameExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getQualifier() == null ? 0 : nodeHashCode(n.getQualifier()));
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        return result;
    }

    @Override
    public Integer visit(final ThisExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getClassExpr() == null ? 0 : nodeHashCode(n.getClassExpr()));
        return result;
    }

    @Override
    public Integer visit(final SuperExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getClassExpr() == null ? 0 : nodeHashCode(n.getClassExpr()));
        return result;
    }

    @Override
    public Integer visit(final UnaryExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getOperator() == null ? 0 : n.getOperator().hashCode());
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        return result;
    }

    @Override
    public Integer visit(final VariableDeclarationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + n.getModifiers();
        result = PRIME * result + (n.getAnnotations() == null ? 0 : nodesHashCode(n.getAnnotations()));
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        result = PRIME * result + (n.getVars() == null ? 0 : nodesHashCode(n.getVars()));
        return result;
    }

    @Override
    public Integer visit(final MarkerAnnotationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        return result;
    }

    @Override
    public Integer visit(final SingleMemberAnnotationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        result = PRIME * result + (n.getMemberValue() == null ? 0 : nodeHashCode(n.getMemberValue()));
        return result;
    }

    @Override
    public Integer visit(final NormalAnnotationExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : nodeHashCode(n.getName()));
        result = PRIME * result + (n.getPairs() == null ? 0 : nodesHashCode(n.getPairs()));
        return result;
    }

    @Override
    public Integer visit(final MemberValuePair n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getName() == null ? 0 : n.getName().hashCode());
        result = PRIME * result + (n.getValue() == null ? 0 : nodeHashCode(n.getValue()));
        return result;
    }

    @Override
    public Integer visit(final ExplicitConstructorInvocationStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        result = PRIME * result + (n.getArgs() == null ? 0 : nodesHashCode(n.getArgs()));
        result = PRIME * result + (n.getTypeArgs() == null ? 0 : nodesHashCode(n.getTypeArgs()));
        return result;
    }

    @Override
    public Integer visit(final TypeDeclarationStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getTypeDeclaration() == null ? 0 : nodeHashCode(n.getTypeDeclaration()));
        return result;
    }

    @Override
    public Integer visit(final AssertStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getCheck() == null ? 0 : nodeHashCode(n.getCheck()));
        result = PRIME * result + (n.getMessage() == null ? 0 : nodeHashCode(n.getMessage()));
        return result;
    }

    @Override
    public Integer visit(final BlockStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getStmts() == null ? 0 : nodesHashCode(n.getStmts()));
        return result;
    }

    @Override
    public Integer visit(final LabeledStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getStmt() == null ? 0 : nodeHashCode(n.getStmt()));
        return result;
    }

    @Override
    public Integer visit(final EmptyStmt n, final Void arg) {
        return 1;
    }

    @Override
    public Integer visit(final ExpressionStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpression() == null ? 0 : nodeHashCode(n.getExpression()));
        return result;
    }

    @Override
    public Integer visit(final SwitchStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getSelector() == null ? 0 : nodeHashCode(n.getSelector()));
        result = PRIME * result + (n.getEntries() == null ? 0 : nodesHashCode(n.getEntries()));
        return result;
    }

    @Override
    public Integer visit(final SwitchEntryStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getLabel() == null ? 0 : nodeHashCode(n.getLabel()));
        result = PRIME * result + (n.getStmts() == null ? 0 : nodesHashCode(n.getStmts()));
        return result;
    }

    @Override
    public Integer visit(final BreakStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getId() == null ? 0 : n.getId().hashCode());
        return result;
    }

    @Override
    public Integer visit(final ReturnStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        return result;
    }

    @Override
    public Integer visit(final IfStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getCondition() == null ? 0 : nodeHashCode(n.getCondition()));
        result = PRIME * result + (n.getThenStmt() == null ? 0 : nodeHashCode(n.getThenStmt()));
        result = PRIME * result + (n.getElseStmt() == null ? 0 : nodeHashCode(n.getElseStmt()));
        return result;
    }

    @Override
    public Integer visit(final WhileStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getCondition() == null ? 0 : nodeHashCode(n.getCondition()));
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        return result;
    }

    @Override
    public Integer visit(final ContinueStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getId() == null ? 0 : n.getId().hashCode());
        return result;
    }

    @Override
    public Integer visit(final DoStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        result = PRIME * result + (n.getCondition() == null ? 0 : nodeHashCode(n.getCondition()));
        return result;
    }

    @Override
    public Integer visit(final ForeachStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getVariable() == null ? 0 : nodeHashCode(n.getVariable()));
        result = PRIME * result + (n.getIterable() == null ? 0 : nodeHashCode(n.getIterable()));
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        return result;
    }

    @Override
    public Integer visit(final ForStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getInit() == null ? 0 : nodesHashCode(n.getInit()));
        result = PRIME * result + (n.getCompare() == null ? 0 : nodeHashCode(n.getCompare()));
        result = PRIME * result + (n.getUpdate() == null ? 0 : nodesHashCode(n.getUpdate()));
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        return result;
    }

    @Override
    public Integer visit(final ThrowStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        return result;
    }

    @Override
    public Integer visit(final SynchronizedStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExpr() == null ? 0 : nodeHashCode(n.getExpr()));
        result = PRIME * result + (n.getBlock() == null ? 0 : nodeHashCode(n.getBlock()));
        return result;
    }

    @Override
    public Integer visit(final TryStmt n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getTryBlock() == null ? 0 : nodeHashCode(n.getTryBlock()));
        result = PRIME * result + (n.getCatchs() == null ? 0 : nodesHashCode(n.getCatchs()));
        result = PRIME * result + (n.getFinallyBlock() == null ? 0 : nodeHashCode(n.getFinallyBlock()));
        return result;
    }

    @Override
    public Integer visit(final CatchClause n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getExcept() == null ? 0 : nodeHashCode(n.getExcept()));
        result = PRIME * result + (n.getCatchBlock() == null ? 0 : nodeHashCode(n.getCatchBlock()));
        return result;
    }

    @Override
    public Integer visit(final LambdaExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getParameters() == null ? 0 : nodesHashCode(n.getParameters()));
        result = PRIME * result + (n.isParametersEnclosed() ? 1231 : 1237);
        result = PRIME * result + (n.getBody() == null ? 0 : nodeHashCode(n.getBody()));
        return result;
    }

    @Override
    public Integer visit(final MethodReferenceExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getScope() == null ? 0 : nodeHashCode(n.getScope()));
        result = PRIME * result + (n.getTypeParameters() == null ? 0 : nodesHashCode(n.getTypeParameters()));
        result = PRIME * result + (n.getIdentifier() == null ? 0 : n.getIdentifier().hashCode());
        return result;
    }

    @Override
    public Integer visit(final TypeExpr n, final Void arg) {
        int result = 1;
        result = PRIME * result + (n.getType() == null ? 0 : nodeHashCode(n.getType()));
        return result;
    }
}
