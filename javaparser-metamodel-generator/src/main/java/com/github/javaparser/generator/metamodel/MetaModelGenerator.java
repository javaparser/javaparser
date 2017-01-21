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
import java.lang.reflect.Field;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.ast.Modifier.FINAL;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

public class MetaModelGenerator {
    private static final String NODE_META_MODEL = "BaseNodeMetaModel";
    private static List<Class<? extends Node>> ALL_MODEL_CLASSES = new ArrayList<Class<? extends Node>>() {{
        /* Base classes go first, so we don't have to do any sorting to make sure
         generated classes can refer to their base generated classes without
         being afraid those are not initialized yet. */
        add(Node.class);

        add(BodyDeclaration.class);
        add(Statement.class);
        add(Expression.class);
        add(Type.class);

        add(AnnotationExpr.class);
        add(TypeDeclaration.class);
        add(LiteralExpr.class);
        add(ReferenceType.class);
        add(StringLiteralExpr.class);

        //
        add(ArrayCreationLevel.class);
        add(CompilationUnit.class);
        add(PackageDeclaration.class);

        add(AnnotationDeclaration.class);
        add(AnnotationMemberDeclaration.class);
        add(ClassOrInterfaceDeclaration.class);
        add(ConstructorDeclaration.class);
        add(EmptyMemberDeclaration.class);
        add(EnumConstantDeclaration.class);
        add(EnumDeclaration.class);
        add(FieldDeclaration.class);
        add(InitializerDeclaration.class);
        add(MethodDeclaration.class);
        add(Parameter.class);
        add(VariableDeclarator.class);

        add(Comment.class);
        add(BlockComment.class);
        add(JavadocComment.class);
        add(LineComment.class);

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
        add(FieldAccessExpr.class);
        add(InstanceOfExpr.class);
        add(IntegerLiteralExpr.class);
        add(LambdaExpr.class);
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
        add(TypeParameter.class);
        add(UnionType.class);
        add(UnknownType.class);
        add(VoidType.class);
        add(WildcardType.class);
    }};

    private static String METAMODEL_PACKAGE = "com.github.javaparser.metamodel";

    public static void main(String[] args) throws IOException, NoSuchMethodException {
        new MetaModelGenerator().run();
    }

    private void run() throws IOException, NoSuchMethodException {
        final Path root = getJavaParserBasePath().resolve(Paths.get("javaparser-metamodel", "src", "main", "java"));

        JavaParser javaParser = new JavaParser();

        SourceRoot sourceRoot = new SourceRoot(root);

        CompilationUnit javaParserMetaModel = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java", javaParser).get();

        generateClassMetaModels(javaParserMetaModel, sourceRoot);

        sourceRoot.saveAll();
    }

    private void generateClassMetaModels(CompilationUnit javaParserMetaModelCu, SourceRoot sourceRoot) throws NoSuchMethodException {
        ClassOrInterfaceDeclaration mmClass = javaParserMetaModelCu.getClassByName("JavaParserMetaModel").get();
        NodeList<Statement> initializeNodeMetaModelsStatements = mmClass.getMethodsByName("initializeNodeMetaModels").get(0).getBody().get().getStatements();
        NodeList<Statement> initializeFieldMetaModelsStatements = mmClass.getMethodsByName("initializeFieldMetaModels").get(0).getBody().get().getStatements();
        initializeNodeMetaModelsStatements.clear();
        initializeFieldMetaModelsStatements.clear();

        for (Class<?> c : ALL_MODEL_CLASSES) {
            String className = metaModelName(c);
            String fieldName = decapitalize(className);
            mmClass.getFieldByName(fieldName).ifPresent(Node::remove);
            FieldDeclaration f = mmClass.addField(className, fieldName, PUBLIC, FINAL);

            Class<?> superclass = c.getSuperclass();
            final String superClassMetaModel = optionalOf(decapitalize(metaModelName(superclass)), isNode(superclass));

            f.getVariable(0).setInitializer(parseExpression(f("new %s(this, %s)", className, superClassMetaModel)));
            initializeNodeMetaModelsStatements.add(parseStatement(f("nodeMetaModels.add(%s);", fieldName)));

            CompilationUnit classMetaModelJavaFile = new CompilationUnit(METAMODEL_PACKAGE);
            classMetaModelJavaFile.addImport("java.util.Optional");
            sourceRoot.add(METAMODEL_PACKAGE, className + ".java", classMetaModelJavaFile);
            ClassOrInterfaceDeclaration classMetaModelClass = classMetaModelJavaFile.addClass(className, PUBLIC);
            classMetaModelClass.addExtendedType(new ClassOrInterfaceType(NODE_META_MODEL));

            AstTypeAnalysis typeAnalysis = new AstTypeAnalysis(c);

            ConstructorDeclaration classMMConstructor = classMetaModelClass
                    .addConstructor()
                    .addParameter("JavaParserMetaModel", "parent")
                    .addParameter("Optional<" + NODE_META_MODEL + ">", "super" + NODE_META_MODEL);
            classMMConstructor
                    .getBody()
                    .addStatement(parseExplicitConstructorInvocationStmt(f("super(super%s, parent, %s.class, \"%s\", \"%s\", %s, %s);",
                            NODE_META_MODEL,
                            c.getName(),
                            c.getSimpleName(),
                            c.getPackage().getName(),
                            typeAnalysis.isAbstract,
                            typeAnalysis.isSelfType)));

            generateFieldMetaModels(c, classMetaModelClass, fieldName, initializeFieldMetaModelsStatements);
        }

        initializeNodeMetaModelsStatements.sort(Comparator.comparing(Node::toString));
    }

    private boolean isNode(Class<?> c) {
        return Node.class.isAssignableFrom(c);
    }

    private void generateFieldMetaModels(Class<?> c, ClassOrInterfaceDeclaration classMetaModelClass, String classMetaModelFieldName, NodeList<Statement> initializeFieldMetaModelsStatements) throws NoSuchMethodException {
        List<Field> fields = new ArrayList<>(Arrays.asList(c.getDeclaredFields()));
        fields.sort(Comparator.comparing(Field::getName));
        for (Field field : fields) {
            if (fieldShouldBeIgnored(field)) {
                continue;
            }

            AstTypeAnalysis fieldAnalysis = new AstTypeAnalysis(c.getMethod(getter(field)).getGenericReturnType());

            Class<?> fieldType = fieldAnalysis.innerType;
            String typeName = fieldType.getTypeName().replace('$', '.');
            String propertyMetaModelFieldName = field.getName() + "PropertyMetaModel";
            classMetaModelClass.addField("PropertyMetaModel", propertyMetaModelFieldName, PUBLIC);
            String propertyInitializer = f("new PropertyMetaModel(%s, \"%s\", %s.class, %s, %s, %s, %s, %s)",
                    classMetaModelFieldName,
                    field.getName(),
                    typeName,
                    optionalOf(decapitalize(metaModelName(fieldType)), isNode(fieldType)),
                    fieldAnalysis.isOptional,
                    fieldAnalysis.isNodeList,
                    fieldAnalysis.isEnumSet,
                    fieldAnalysis.isSelfType);
            String fieldSetting = f("%s.%s=%s;", classMetaModelFieldName, propertyMetaModelFieldName, propertyInitializer);
            String fieldAddition = f("%s.getPropertyMetaModels().add(%s.%s);", classMetaModelFieldName, classMetaModelFieldName, propertyMetaModelFieldName);

            initializeFieldMetaModelsStatements.add(parseStatement(fieldSetting));
            initializeFieldMetaModelsStatements.add(parseStatement(fieldAddition));
        }
    }

    private String getter(Field field) {
        return getterName(field.getType(), field.getName());
    }

    private static String metaModelName(Class<?> c) {
        return c.getSimpleName() + "MetaModel";
    }

    private boolean fieldShouldBeIgnored(Field reflectionField) {
        if (java.lang.reflect.Modifier.isStatic(reflectionField.getModifiers())) {
            return true;
        }
        String name = reflectionField.getName();
        switch (name) {
            case "parentNode":
            case "observers":
            case "innerList":
            case "data":
            case "range":
            case "childNodes":
            case "orphanComments":
                return true;
        }
        return false;
    }

}
