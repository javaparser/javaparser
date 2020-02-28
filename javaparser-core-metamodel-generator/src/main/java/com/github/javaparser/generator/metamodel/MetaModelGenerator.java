/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.*;
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

    static final String COPYRIGHT_NOTICE_JP_CORE = "\n" +
        " * Copyright (C) 2007-2010 Júlio Vilmar Gesser.\n" +
        " * Copyright (C) 2011, 2013-2020 The JavaParser Team.\n" +
        " *\n" +
        " * This file is part of JavaParser.\n" +
        " *\n" +
        " * JavaParser can be used either under the terms of\n" +
        " * a) the GNU Lesser General Public License as published by\n" +
        " *     the Free Software Foundation, either version 3 of the License, or\n" +
        " *     (at your option) any later version.\n" +
        " * b) the terms of the Apache License\n" +
        " *\n" +
        " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
        " * LICENCE.APACHE. Please refer to those files for details.\n" +
        " *\n" +
        " * JavaParser is distributed in the hope that it will be useful,\n" +
        " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
        " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
        " * GNU Lesser General Public License for more details.\n" +
        " ";

    static final String COPYRIGHT_NOTICE_JP_SS = "\n" +
        " * Copyright (C) 2015-2016 Federico Tomassetti\n" +
        " * Copyright (C) 2017-2020 The JavaParser Team.\n" +
        " *\n" +
        " * This file is part of JavaParser.\n" +
        " *\n" +
        " * JavaParser can be used either under the terms of\n" +
        " * a) the GNU Lesser General Public License as published by\n" +
        " *     the Free Software Foundation, either version 3 of the License, or\n" +
        " *     (at your option) any later version.\n" +
        " * b) the terms of the Apache License\n" +
        " *\n" +
        " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
        " * LICENCE.APACHE. Please refer to those files for details.\n" +
        " *\n" +
        " * JavaParser is distributed in the hope that it will be useful,\n" +
        " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
        " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
        " * GNU Lesser General Public License for more details.\n" +
        " ";

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

        add(JavadocContent.class);
        add(JavadocDescription.class);
        add(JavadocBlockTag.class);
        add(JavadocDescriptionElement.class);
        add(JavadocSnippet.class);
        add(JavadocInlineTag.class);

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
        add(TextBlockLiteralExpr.class);
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
        add(YieldStmt.class);
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
        final CompilationUnit javaParserMetaModelCu = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java");
        javaParserMetaModelCu.setBlockComment(COPYRIGHT_NOTICE_JP_CORE);

        generateNodeMetaModels(javaParserMetaModelCu, sourceRoot);
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
