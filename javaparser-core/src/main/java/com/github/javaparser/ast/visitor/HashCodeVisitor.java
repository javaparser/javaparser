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

public class HashCodeVisitor implements GenericVisitor<Integer, Void> {
    @Override
    public Integer visit(CompilationUnit n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(PackageDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(TypeParameter n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(LineComment n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BlockComment n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ClassOrInterfaceDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(EnumDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(EnumConstantDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(AnnotationDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(AnnotationMemberDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(FieldDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(VariableDeclarator n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ConstructorDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(MethodDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(Parameter n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(EmptyMemberDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(InitializerDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(JavadocComment n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ClassOrInterfaceType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(PrimitiveType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ArrayType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ArrayCreationLevel n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(IntersectionType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(UnionType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(VoidType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(WildcardType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(UnknownType n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ArrayAccessExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ArrayCreationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ArrayInitializerExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(AssignExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BinaryExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(CastExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ClassExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ConditionalExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(EnclosedExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(FieldAccessExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(InstanceOfExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(StringLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(IntegerLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(LongLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(CharLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(DoubleLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BooleanLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(NullLiteralExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(MethodCallExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(NameExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ObjectCreationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ThisExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SuperExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(UnaryExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(VariableDeclarationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(MarkerAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SingleMemberAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(NormalAnnotationExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(MemberValuePair n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(TypeDeclarationStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(AssertStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BlockStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(LabeledStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(EmptyStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ExpressionStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SwitchStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SwitchEntryStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BreakStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ReturnStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(IfStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(WhileStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ContinueStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(DoStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ForeachStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ForStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(ThrowStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SynchronizedStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(TryStmt n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(CatchClause n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(LambdaExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(MethodReferenceExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(TypeExpr n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(NodeList n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(BadImportDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SingleStaticImportDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SingleTypeImportDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(StaticImportOnDemandDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(TypeImportOnDemandDeclaration n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(Name n, Void arg) {
        return null;
    }

    @Override
    public Integer visit(SimpleName n, Void arg) {
        return null;
    }
}
