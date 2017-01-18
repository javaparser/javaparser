package com.github.javaparser.generator.metamodel;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.WildcardType;
import com.github.javaparser.generator.utils.SourceRoot;

import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.ast.Modifier.FINAL;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.utils.GeneratorUtils.capitalize;
import static com.github.javaparser.generator.utils.GeneratorUtils.decapitalize;
import static com.github.javaparser.generator.utils.GeneratorUtils.f;

public class MetaModelGenerator {
    private static List<Class<?>> ALL_MODEL_CLASSES = new ArrayList<Class<?>>() {{
        add(NodeList.class);

        // Base classes go first.
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

    public static String METAMODEL_PACKAGE = "com.github.javaparser.metamodel";

    public static void main(String[] args) throws IOException, NoSuchMethodException {
        new MetaModelGenerator().run();
    }

    private void run() throws IOException, NoSuchMethodException {
        String path = MetaModelGenerator.class.getProtectionDomain().getCodeSource().getLocation().getPath();
        if (path.charAt(2) == ':') {
            path = path.substring(1);
        }
        final Path root = Paths.get(path, "..", "..", "..", "javaparser-core", "src", "main", "java");

        JavaParser javaParser = new JavaParser();

        SourceRoot sourceRoot = new SourceRoot(root);

        CompilationUnit javaParserMetaModel = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java", javaParser).get();

        ClassOrInterfaceDeclaration mmClass = javaParserMetaModel.getClassByName("JavaParserMetaModel").get();
        BlockStmt constructor = mmClass.getDefaultConstructor().get().getBody();
        constructor.getStatements().clear();

        for (Class<?> c : ALL_MODEL_CLASSES) {
            String className = metaModelName(c);
            String fieldName = decapitalize(className);
            mmClass.getFieldByName(fieldName).ifPresent(Node::remove);
            FieldDeclaration f = mmClass.addField("ClassMetaModel", fieldName, PUBLIC, FINAL);

            Class<?> superclass = c.getSuperclass();
            final String superClassMetaModel;
            if (Node.class.isAssignableFrom(superclass)) {
                superClassMetaModel = f("Optional.of(%s)", decapitalize(metaModelName(superclass)));
            } else {
                superClassMetaModel = "Optional.empty()";
            }


            f.getVariable(0).setInitializer(parseExpression(f("new %s(this, %s)", className, superClassMetaModel)));
            constructor.addStatement(parseStatement(f("classMetaModels.add(%s);", fieldName)));


            CompilationUnit classMetaModelJavaFile = new CompilationUnit(METAMODEL_PACKAGE);
            classMetaModelJavaFile.addImport("java.util.Optional");
            sourceRoot.add(METAMODEL_PACKAGE, className + ".java", classMetaModelJavaFile);
            ClassOrInterfaceDeclaration classMetaModelClass = classMetaModelJavaFile.addClass(className, PUBLIC);
            classMetaModelClass.addExtendedType(new ClassOrInterfaceType("ClassMetaModel"));

            ConstructorDeclaration classMMConstructor = classMetaModelClass
                    .addConstructor()
                    .addParameter("JavaParserMetaModel", "parent")
                    .addParameter("Optional<ClassMetaModel>", "superClassMetaModel");
            classMMConstructor
                    .getBody()
                    .addStatement(parseExplicitConstructorInvocationStmt(f("super(superClassMetaModel, parent, %s.class, \"%s\", \"%s\", \"%s\", %s);", c.getName(), c.getSimpleName(), c.getName(), c.getPackage().getName(), java.lang.reflect.Modifier.isAbstract(c.getModifiers()))));

            // FIXME parent's fields too!!!
            List<Field> fields = new ArrayList<>(Arrays.asList(c.getDeclaredFields()));
            fields.sort(Comparator.comparing(Field::getName));
            boolean anyFieldsGenerated = false;
            for (Field field : fields) {
                if (!isPartOfModel(field)) {
                    continue;
                }
                boolean isOptional = false;
                boolean isEnumSet = false;
                boolean isNodeList = false;
                boolean hasWildcard = false;
                boolean ignore = false;

                java.lang.reflect.Type fieldType = c.getMethod(getter(field)).getGenericReturnType();

                while (fieldType instanceof ParameterizedType) {
                    ParameterizedType t = (ParameterizedType) fieldType;
                    java.lang.reflect.Type currentOuterType = t.getRawType();
                    if (currentOuterType == java.util.List.class) {
                        ignore = true;
                    }
                    if (currentOuterType == NodeList.class) {
                        isNodeList = true;
                    }
                    if (currentOuterType == Optional.class) {
                        isOptional = true;
                    }
                    if (currentOuterType == EnumSet.class) {
                        isEnumSet = true;
                    }

                    if (t.getActualTypeArguments()[0] instanceof java.lang.reflect.WildcardType) {
                        fieldType = t.getRawType();
                        hasWildcard = true;
                        break;
                    }
                    fieldType = t.getActualTypeArguments()[0];
                }

                if (ignore) {
                    continue;
                }

                String fieldAddition = f("fieldMetaModels.add(new FieldMetaModel(this, \"%s\", \"%s\", \"%s\", %s.class, getField(\"%s\"), true, %s, %s, %s, %s));",
                        getter(field),
                        setter(field),
                        field.getName(),
                        fieldType.getTypeName().replace('$', '.'),
                        field.getName(),
                        isOptional,
                        isNodeList,
                        isEnumSet,
                        hasWildcard);

                classMMConstructor.getBody().addStatement(fieldAddition);
                anyFieldsGenerated = true;
            }
            if (anyFieldsGenerated) {
                classMetaModelJavaFile.addImport("java.lang.reflect.Field");
                classMetaModelJavaFile.addImport(c);
                classMetaModelClass.addMember(parseClassBodyDeclaration(f("private Field getField(String name) {\n" +
                        "        try {\n" +
                        "            return %s.class.getDeclaredField(name);\n" +
                        "        } catch (NoSuchFieldException e) {\n" +
                        "            throw new RuntimeException(e);\n" +
                        "        }\n" +
                        "    }\n", c.getSimpleName())));
            }
        }

        constructor.getStatements().sort(Comparator.comparing(o -> ((NameExpr) ((MethodCallExpr) ((ExpressionStmt) o).getExpression()).getArgument(0)).getNameAsString()));

        sourceRoot.saveAll();
    }

    private String setter(Field field) {
        return "set" + capitalize(field.getName());
    }

    private String getter(Field field) {
        String name = field.getName();
        if (field.getName().startsWith("is")) {
            return field.getName();
        } else if (field.getType().equals(Boolean.class)) {
            return "is" + capitalize(name);
        }
        return "get" + capitalize(name);
    }

    private static String metaModelName(Class<?> c) {
        return c.getSimpleName() + "MetaModel";
    }

    boolean isPartOfModel(Field reflectionField) {
        if (java.lang.reflect.Modifier.isStatic(reflectionField.getModifiers())) {
            return false;
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
                return false;
        }
        return true;
    }

}
