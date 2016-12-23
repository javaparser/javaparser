package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

/**
 * Calculates a hash code for a node and its children.
 */
public class HashCodeVisitor implements GenericVisitor<Integer, Void> {

    public Integer visit(AnnotationDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(AnnotationMemberDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getDefaultValue().isPresent() ? n.getDefaultValue().get().accept(this, arg) : 0) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(ArrayAccessExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getIndex().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ArrayCreationExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getElementType().accept(this, arg)) * 31 + (n.getInitializer().isPresent() ? n.getInitializer().get().accept(this, arg) : 0) * 31 + (n.getLevels().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ArrayCreationLevel n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getDimension().isPresent() ? n.getDimension().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ArrayInitializerExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValues().accept(this, arg));
    }

    public Integer visit(ArrayType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getComponentType().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(AssertStmt n, Void arg) {
        return (n.getCheck().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getMessage().isPresent() ? n.getMessage().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(AssignExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOperator().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getTarget().accept(this, arg)) * 31 + (n.getValue().accept(this, arg));
    }

    public Integer visit(BadImportDeclaration n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(BinaryExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getLeft().accept(this, arg)) * 31 + (n.getOperator().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getRight().accept(this, arg));
    }

    public Integer visit(BlockComment n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getCommentedNode().isPresent() ? n.getCommentedNode().get().accept(this, arg) : 0) * 31 + (n.getContent().hashCode()) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(BlockStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getStatements().accept(this, arg));
    }

    public Integer visit(BooleanLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue() ? 1 : 0);
    }

    public Integer visit(BreakStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(CastExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(CatchClause n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getParameter().accept(this, arg));
    }

    public Integer visit(CharLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().hashCode());
    }

    public Integer visit(ClassExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(ClassOrInterfaceDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getExtendedTypes().accept(this, arg)) * 31 + (n.getImplementedTypes().accept(this, arg)) * 31 + (n.isInterface() ? 1 : 0) * 31 + (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getTypeParameters().accept(this, arg));
    }

    public Integer visit(ClassOrInterfaceType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(CompilationUnit n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getImports().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getPackageDeclaration().isPresent() ? n.getPackageDeclaration().get().accept(this, arg) : 0) * 31 + (n.getTypes().accept(this, arg));
    }

    public Integer visit(ConditionalExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getElseExpr().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getThenExpr().accept(this, arg));
    }

    public Integer visit(ConstructorDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getParameters().accept(this, arg)) * 31 + (n.getThrownExceptions().accept(this, arg)) * 31 + (n.getTypeParameters().accept(this, arg));
    }

    public Integer visit(ContinueStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(DoStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(DoubleLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().hashCode());
    }

    public Integer visit(EmptyMemberDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(EmptyStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(EnclosedExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getInner().isPresent() ? n.getInner().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(EnumConstantDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getArguments().accept(this, arg)) * 31 + (n.getClassBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(EnumDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getEntries().accept(this, arg)) * 31 + (n.getImplementedTypes().accept(this, arg)) * 31 + (n.getMembers().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return (n.getArguments().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getExpression().isPresent() ? n.getExpression().get().accept(this, arg) : 0) * 31 + (n.isThis() ? 1 : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(ExpressionStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(FieldAccessExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getField().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(FieldDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getVariables().accept(this, arg));
    }

    public Integer visit(ForStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getCompare().isPresent() ? n.getCompare().get().accept(this, arg) : 0) * 31 + (n.getInitialization().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getUpdate().accept(this, arg));
    }

    public Integer visit(ForeachStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getIterable().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getVariable().accept(this, arg));
    }

    public Integer visit(IfStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getElseStmt().isPresent() ? n.getElseStmt().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getThenStmt().accept(this, arg));
    }

    public Integer visit(InitializerDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.isStatic() ? 1 : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(InstanceOfExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(IntegerLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().hashCode());
    }

    public Integer visit(IntersectionType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getElements().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(JavadocComment n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getCommentedNode().isPresent() ? n.getCommentedNode().get().accept(this, arg) : 0) * 31 + (n.getContent().hashCode()) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(LabeledStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getLabel().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getStatement().accept(this, arg));
    }

    public Integer visit(LambdaExpr n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.isEnclosingParameters() ? 1 : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getParameters().accept(this, arg));
    }

    public Integer visit(LineComment n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getCommentedNode().isPresent() ? n.getCommentedNode().get().accept(this, arg) : 0) * 31 + (n.getContent().hashCode()) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(LocalClassDeclarationStmt n, Void arg) {
        return (n.getClassDeclaration().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(LongLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().hashCode());
    }

    public Integer visit(MarkerAnnotationExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(MemberValuePair n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().accept(this, arg));
    }

    public Integer visit(MethodCallExpr n, Void arg) {
        return (n.getArguments().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getScope().accept(this, arg)) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(MethodDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getBody().isPresent() ? n.getBody().get().accept(this, arg) : 0) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.isDefault() ? 1 : 0) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getParameters().accept(this, arg)) * 31 + (n.getThrownExceptions().accept(this, arg)) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getTypeParameters().accept(this, arg));
    }

    public Integer visit(MethodReferenceExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getIdentifier().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getScope().accept(this, arg)) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(Name n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getIdentifier().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getQualifier().isPresent() ? n.getQualifier().get().accept(this, arg) : 0);
    }

    public Integer visit(NameExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(NodeList n, Void arg) {
        return n.hashCode();
    }

    public Integer visit(NormalAnnotationExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getPairs().accept(this, arg));
    }

    public Integer visit(NullLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ObjectCreationExpr n, Void arg) {
        return (n.getAnonymousClassBody().isPresent() ? n.getAnonymousClassBody().get().accept(this, arg) : 0) * 31 + (n.getArguments().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getScope().isPresent() ? n.getScope().get().accept(this, arg) : 0) * 31 + (n.getType().accept(this, arg)) * 31 + (n.getTypeArguments().isPresent() ? n.getTypeArguments().get().accept(this, arg) : 0);
    }

    public Integer visit(PackageDeclaration n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(Parameter n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.isVarArgs() ? 1 : 0) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(PrimitiveType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().hashCode());
    }

    public Integer visit(ReturnStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().isPresent() ? n.getExpression().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(SimpleName n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getIdentifier().hashCode()) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(SingleMemberAnnotationExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getMemberValue().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(SingleStaticImportDeclaration n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getStaticMember().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(SingleTypeImportDeclaration n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(StaticImportOnDemandDeclaration n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(StringLiteralExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getValue().hashCode());
    }

    public Integer visit(SuperExpr n, Void arg) {
        return (n.getClassExpr().isPresent() ? n.getClassExpr().get().accept(this, arg) : 0) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(SwitchEntryStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getLabel().isPresent() ? n.getLabel().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getStatements().accept(this, arg));
    }

    public Integer visit(SwitchStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getEntries().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getSelector().accept(this, arg));
    }

    public Integer visit(SynchronizedStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ThisExpr n, Void arg) {
        return (n.getClassExpr().isPresent() ? n.getClassExpr().get().accept(this, arg) : 0) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(ThrowStmt n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(TryStmt n, Void arg) {
        return (n.getCatchClauses().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getFinallyBlock().isPresent() ? n.getFinallyBlock().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getResources().accept(this, arg)) * 31 + (n.getTryBlock().isPresent() ? n.getTryBlock().get().accept(this, arg) : 0);
    }

    public Integer visit(TypeExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(TypeImportOnDemandDeclaration n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(TypeParameter n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getTypeBound().accept(this, arg));
    }

    public Integer visit(UnaryExpr n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getExpression().accept(this, arg)) * 31 + (n.getOperator().hashCode()) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(UnionType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getElements().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(UnknownType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(VariableDeclarationExpr n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getModifiers().hashCode()) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getVariables().accept(this, arg));
    }

    public Integer visit(VariableDeclarator n, Void arg) {
        return (n.getComment().accept(this, arg)) * 31 + (n.getInitializer().isPresent() ? n.getInitializer().get().accept(this, arg) : 0) * 31 + (n.getName().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getType().accept(this, arg));
    }

    public Integer visit(VoidType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(WhileStmt n, Void arg) {
        return (n.getBody().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getCondition().accept(this, arg)) * 31 + (n.getOrphanComments().hashCode());
    }

    public Integer visit(WildcardType n, Void arg) {
        return (n.getAnnotations().accept(this, arg)) * 31 + (n.getComment().accept(this, arg)) * 31 + (n.getExtendedTypes().isPresent() ? n.getExtendedTypes().get().accept(this, arg) : 0) * 31 + (n.getOrphanComments().hashCode()) * 31 + (n.getSuperTypes().isPresent() ? n.getSuperTypes().get().accept(this, arg) : 0);
    }
}

