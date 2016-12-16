package com.github.javaparser.model;

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * The model contains meta-data about all nodes in the AST.
 * You can base source code generators on it.
 */
public class JavaParserModel {
    private static Set<Class<? extends Node>> ALL_NODE_CLASSES = new HashSet<Class<? extends Node>>() {{
        add(ArrayCreationLevel.class);
        add(CompilationUnit.class);
        add(Node.class);
        add(PackageDeclaration.class);

        add(AnnotationDeclaration.class);
        add(AnnotationMemberDeclaration.class);
        add(BodyDeclaration.class);
        add(ClassOrInterfaceDeclaration.class);
        add(ConstructorDeclaration.class);
        add(EmptyMemberDeclaration.class);
        add(EnumConstantDeclaration.class);
        add(EnumDeclaration.class);
        add(FieldDeclaration.class);
        add(InitializerDeclaration.class);
        add(MethodDeclaration.class);
        add(Parameter.class);
        add(TypeDeclaration.class);
        add(VariableDeclarator.class);

        add(BlockComment.class);
        add(Comment.class);
        add(JavadocComment.class);
        add(LineComment.class);

        add(AnnotationExpr.class);
        add(ArrayAccessExpr.class);
        add(ArrayCreationExpr.class);
        add(ArrayInitializerExpr.class);
        add(AssignExpr.class);
        add(BinaryExpr.class);
        add(BooleanLiteralExpr.class);
        add(CastExpr.class);
        add(CharLiteralExpr.class);
        add(ClassExpr.class);
        add(ConditionalExpr.class);
        add(DoubleLiteralExpr.class);
        add(EnclosedExpr.class);
        add(Expression.class);
        add(FieldAccessExpr.class);
        add(InstanceOfExpr.class);
        add(IntegerLiteralExpr.class);
        add(LambdaExpr.class);
        add(LiteralExpr.class);
        add(LongLiteralExpr.class);
        add(MarkerAnnotationExpr.class);
        add(MemberValuePair.class);
        add(MethodCallExpr.class);
        add(MethodReferenceExpr.class);
        add(NameExpr.class);
        add(Name.class);
        add(NormalAnnotationExpr.class);
        add(NullLiteralExpr.class);
        add(ObjectCreationExpr.class);
        add(SimpleName.class);
        add(SingleMemberAnnotationExpr.class);
        add(StringLiteralExpr.class);
        add(SuperExpr.class);
        add(ThisExpr.class);
        add(TypeExpr.class);
        add(UnaryExpr.class);
        add(VariableDeclarationExpr.class);

        add(BadImportDeclaration.class);
        add(ImportDeclaration.class);
        add(SingleStaticImportDeclaration.class);
        add(SingleTypeImportDeclaration.class);
        add(StaticImportOnDemandDeclaration.class);
        add(TypeImportOnDemandDeclaration.class);

        add(AssertStmt.class);
        add(BlockStmt.class);
        add(BreakStmt.class);
        add(CatchClause.class);
        add(ContinueStmt.class);
        add(DoStmt.class);
        add(EmptyStmt.class);
        add(ExplicitConstructorInvocationStmt.class);
        add(ExpressionStmt.class);
        add(ForeachStmt.class);
        add(ForStmt.class);
        add(IfStmt.class);
        add(LabeledStmt.class);
        add(ReturnStmt.class);
        add(Statement.class);
        add(SwitchEntryStmt.class);
        add(SwitchStmt.class);
        add(SynchronizedStmt.class);
        add(ThrowStmt.class);
        add(TryStmt.class);
        add(TypeDeclarationStmt.class);
        add(WhileStmt.class);

        add(ArrayType.class);
        add(ClassOrInterfaceType.class);
        add(IntersectionType.class);
        add(PrimitiveType.class);
        add(ReferenceType.class);
        add(Type.class);
        add(TypeParameter.class);
        add(UnionType.class);
        add(UnknownType.class);
        add(VoidType.class);
        add(WildcardType.class);
    }};

    private final Set<NodeModel> nodeModels = new HashSet<>();

    public JavaParserModel() {
        for (Class<? extends Node> nodeClass : ALL_NODE_CLASSES) {
            nodeModels.add(new NodeModel(this, nodeClass));
        }
        nodeModels.forEach(NodeModel::initialize);
    }

    public Set<NodeModel> getNodeModels() {
        return nodeModels;
    }

    public Optional<NodeModel> getNodeModel(Class<?> c) {
        for (NodeModel nodeModel : nodeModels) {
            if (nodeModel.getNodeClass().equals(c)) {
                return Optional.of(nodeModel);
            }
        }
        return Optional.empty();
    }
}
