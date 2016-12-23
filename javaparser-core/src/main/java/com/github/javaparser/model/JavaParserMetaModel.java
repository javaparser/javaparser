package com.github.javaparser.model;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.imports.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

/**
 * The model contains meta-data about all nodes in the AST.
 * You can base source code generators on it.
 */
public class JavaParserMetaModel {
    private static List<Class<?>> ALL_MODEL_CLASSES = new ArrayList<Class<?>>() {{
        add(ArrayCreationLevel.class);
        add(CompilationUnit.class);
        add(Node.class);
        add(PackageDeclaration.class);
        add(NodeList.class);

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
        add(LocalClassDeclarationStmt.class);
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

    static {
        ALL_MODEL_CLASSES.sort(Comparator.comparing(Class::getSimpleName));
    }

    private final List<ClassMetaModel> classMetaModels = new ArrayList<>();

    public JavaParserMetaModel() {
        for (Class<?> nodeClass : ALL_MODEL_CLASSES) {
            classMetaModels.add(new ClassMetaModel(this, nodeClass));
        }
        classMetaModels.forEach(ClassMetaModel::initialize);
    }

    public List<ClassMetaModel> getClassMetaModels() {
        return classMetaModels;
    }

    public Optional<ClassMetaModel> getClassMetaModel(Class<?> c) {
        for (ClassMetaModel classMetaModel : classMetaModels) {
            if (classMetaModel.getReflectionClass().equals(c)) {
                return Optional.of(classMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (ClassMetaModel classMetaModel : getClassMetaModels()) {
            b.append(classMetaModel).append("\n");
            for (FieldMetaModel fieldMetaModel : classMetaModel.getFieldMetaModels()) {
                b.append("\t").append(fieldMetaModel).append("\n");
            }
        }
        return b.toString();
    }
}
