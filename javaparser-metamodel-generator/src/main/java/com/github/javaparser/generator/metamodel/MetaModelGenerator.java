package com.github.javaparser.generator.metamodel;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.generator.utils.SourceRoot;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.ast.Modifier.FINAL;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.utils.GeneratorUtils.decapitalize;
import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public class MetaModelGenerator {
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

        add(ImportDeclaration.class);

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

    public static String METAMODEL_PACKAGE = "com.github.javaparser.metamodel";

    public static void main(String[] args) throws IOException {
        final Path root = Paths.get(MetaModelGenerator.class.getProtectionDomain().getCodeSource().getLocation().getPath(), "..", "..", "..", "javaparser-core", "src", "main", "java");

        JavaParser javaParser = new JavaParser();

        SourceRoot sourceRoot = new SourceRoot(root);

        CompilationUnit javaParserMetaModel = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java", javaParser).get();

        ClassOrInterfaceDeclaration mmClass = javaParserMetaModel.getClassByName("JavaParserMetaModel").get();
        BlockStmt constructor = mmClass.getDefaultConstructor().get().getBody();
        constructor.getStatements().clear();

        for (Class<?> c : ALL_MODEL_CLASSES) {
            String className = c.getSimpleName() + "MetaModel";
            String fieldName = decapitalize(className);
            mmClass.getFieldByName(fieldName).ifPresent(Node::remove);
            FieldDeclaration f = mmClass.addField("ClassMetaModel", fieldName, PUBLIC, FINAL);
            f.getVariable(0).setInitializer(parseExpression(f("new %s(this)", className)));
            constructor.addStatement(parseStatement(f("classMetaModels.add(%s);", fieldName)));

            CompilationUnit classMetaModelJavaFile = new CompilationUnit(METAMODEL_PACKAGE);
            sourceRoot.add(METAMODEL_PACKAGE, className + ".java", classMetaModelJavaFile);
            ClassOrInterfaceDeclaration classMetaModelClass = classMetaModelJavaFile.addClass(className, PUBLIC);
            classMetaModelClass.addExtendedType(new ClassOrInterfaceType("ClassMetaModel"));
            classMetaModelClass.addMember(parseClassBodyDeclaration(f("public %s(JavaParserMetaModel parent) { super(null, parent, null, null, null, null, false); }", className)));
        }


        System.out.println(javaParserMetaModel);
        sourceRoot.saveAll();
    }
}
