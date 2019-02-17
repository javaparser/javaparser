package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import com.github.javaparser.utils.SourceRoot;

import java.lang.reflect.Field;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.utils.Utils.decapitalize;

public class MetaModelGenerator {
    static final String BASE_NODE_META_MODEL = "BaseNodeMetaModel";
    private static List<Class<? extends Node>> ALL_NODE_CLASSES = new ArrayList<Class<? extends Node>>() {{
        /* Base classes go first, so we don't have to do any sorting to make sure
         generated classes can refer to their base generated classes without
         being afraid those are not initialized yet. */
        add(Node.class);

        add(BodyDeclaration.class);
        add(CallableDeclaration.class);
        add(Statement.class);
        add(Expression.class);
        add(Type.class);

        add(AnnotationExpr.class);
        add(TypeDeclaration.class);
        add(ReferenceType.class);

        add(LiteralExpr.class);
        add(LiteralStringValueExpr.class);
        add(StringLiteralExpr.class);

        add(ModuleDeclaration.class);
        add(ModuleDirective.class);

        //
        add(ArrayCreationLevel.class);
        add(CompilationUnit.class);
        add(PackageDeclaration.class);
        add(Modifier.class);

        add(AnnotationDeclaration.class);
        add(AnnotationMemberDeclaration.class);
        add(ClassOrInterfaceDeclaration.class);
        add(ConstructorDeclaration.class);
        add(EnumConstantDeclaration.class);
        add(EnumDeclaration.class);
        add(FieldDeclaration.class);
        add(InitializerDeclaration.class);
        add(MethodDeclaration.class);
        add(Parameter.class);
        add(ReceiverParameter.class);
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
        add(SwitchExpr.class);

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
        add(ForEachStmt.class);
        add(ForStmt.class);
        add(IfStmt.class);
        add(LabeledStmt.class);
        add(ReturnStmt.class);
        add(SwitchEntry.class);
        add(SwitchStmt.class);
        add(SynchronizedStmt.class);
        add(ThrowStmt.class);
        add(TryStmt.class);
        add(LocalClassDeclarationStmt.class);
        add(WhileStmt.class);
        add(UnparsableStmt.class);

        add(ArrayType.class);
        add(ClassOrInterfaceType.class);
        add(IntersectionType.class);
        add(PrimitiveType.class);
        add(TypeParameter.class);
        add(UnionType.class);
        add(UnknownType.class);
        add(VoidType.class);
        add(WildcardType.class);
        add(VarType.class);

        add(ModuleRequiresDirective.class);
        add(ModuleExportsDirective.class);
        add(ModuleProvidesDirective.class);
        add(ModuleUsesDirective.class);
        add(ModuleOpensDirective.class);
    }};

    static String METAMODEL_PACKAGE = "com.github.javaparser.metamodel";

    public static void main(String[] args) throws NoSuchMethodException {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.RAW)
                .setStoreTokens(false);
        final SourceRoot sourceRoot = new SourceRoot(root, parserConfiguration);
        sourceRoot.setPrinter(new PrettyPrinter(new PrettyPrinterConfiguration().setEndOfLineCharacter("\n"))::print);
        StaticJavaParser.setConfiguration(parserConfiguration);

        new MetaModelGenerator().run(sourceRoot);

        sourceRoot.saveAll();
    }

    private void run(SourceRoot sourceRoot) throws NoSuchMethodException {
        final CompilationUnit javaParserMetaModel = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java");

        generateNodeMetaModels(javaParserMetaModel, sourceRoot);
    }

    private void generateNodeMetaModels(CompilationUnit javaParserMetaModelCu, SourceRoot sourceRoot) throws NoSuchMethodException {
        final ClassOrInterfaceDeclaration metaModelCoid = javaParserMetaModelCu.getClassByName("JavaParserMetaModel").get();
        final NodeList<Statement> initializeNodeMetaModelsStatements = metaModelCoid.getMethodsByName("initializeNodeMetaModels").get(0).getBody().get().getStatements();
        final NodeList<Statement> initializePropertyMetaModelsStatements = metaModelCoid.getMethodsByName("initializePropertyMetaModels").get(0).getBody().get().getStatements();
        final NodeList<Statement> initializeConstructorParametersStatements = metaModelCoid.getMethodsByName("initializeConstructorParameters").get(0).getBody().get().getStatements();
        initializeNodeMetaModelsStatements.clear();
        initializePropertyMetaModelsStatements.clear();
        initializeConstructorParametersStatements.clear();

        metaModelCoid.getFields().stream().filter(f -> f.getVariable(0).getNameAsString().endsWith("MetaModel")).forEach(Node::remove);
        final NodeMetaModelGenerator nodeMetaModelGenerator = new NodeMetaModelGenerator();
        for (Class<? extends Node> nodeClass : ALL_NODE_CLASSES) {
            nodeMetaModelGenerator.generate(nodeClass, metaModelCoid, initializeNodeMetaModelsStatements, initializePropertyMetaModelsStatements, initializeConstructorParametersStatements, sourceRoot);
        }

        initializeNodeMetaModelsStatements.sort(Comparator.comparing(Node::toString));
    }

    static boolean isNode(Class<?> c) {
        return Node.class.isAssignableFrom(c);
    }

    static String nodeMetaModelName(Class<?> c) {
        return c.getSimpleName() + "MetaModel";
    }

    static String propertyMetaModelFieldName(Field field) {
        return field.getName() + "PropertyMetaModel";
    }

    static String nodeMetaModelFieldName(Class<?> nodeClass) {
        return decapitalize(nodeMetaModelName(nodeClass));
    }

}
