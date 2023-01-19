/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.CompactConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.generator.AbstractGenerator;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.Printer;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration.ConfigOption;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.SourceRoot;

import java.lang.reflect.Field;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.utils.Utils.decapitalize;

public class MetaModelGenerator extends AbstractGenerator {

    static final String BASE_NODE_META_MODEL = "BaseNodeMetaModel";
    static final String METAMODEL_PACKAGE = "com.github.javaparser.metamodel";

    /**
     * Note that order of this list is manually set and maintained.
     */
    private static final List<Class<? extends Node>> ALL_NODE_CLASSES = new ArrayList<Class<? extends Node>>() {{
        /* Base classes go first, so we don't have to do any sorting to make sure
         generated classes can refer to their base generated classes without
         being afraid those are not initialized yet. */

        // Fully qualified names used to make logical groupings (somewhat) more explicit.

        //
        add(com.github.javaparser.ast.Node.class);

        add(com.github.javaparser.ast.body.BodyDeclaration.class);
        add(com.github.javaparser.ast.body.CallableDeclaration.class);
        add(com.github.javaparser.ast.expr.Expression.class);
        add(com.github.javaparser.ast.stmt.Statement.class);
        add(com.github.javaparser.ast.type.Type.class);

        add(com.github.javaparser.ast.expr.AnnotationExpr.class);
        add(com.github.javaparser.ast.type.ReferenceType.class);
        add(com.github.javaparser.ast.body.TypeDeclaration.class);

        add(com.github.javaparser.ast.expr.LiteralExpr.class);
        add(com.github.javaparser.ast.expr.LiteralStringValueExpr.class);
        add(com.github.javaparser.ast.expr.StringLiteralExpr.class);

        add(com.github.javaparser.ast.modules.ModuleDeclaration.class);
        add(com.github.javaparser.ast.modules.ModuleDirective.class);

        //
        add(com.github.javaparser.ast.ArrayCreationLevel.class);
        add(com.github.javaparser.ast.CompilationUnit.class);
        add(com.github.javaparser.ast.ImportDeclaration.class);
        add(com.github.javaparser.ast.Modifier.class);
        add(com.github.javaparser.ast.PackageDeclaration.class);

        //
        add(com.github.javaparser.ast.body.AnnotationDeclaration.class);
        add(com.github.javaparser.ast.body.AnnotationMemberDeclaration.class);
        add(com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class);
        add(com.github.javaparser.ast.body.ConstructorDeclaration.class);
        add(com.github.javaparser.ast.body.EnumConstantDeclaration.class);
        add(com.github.javaparser.ast.body.EnumDeclaration.class);
        add(com.github.javaparser.ast.body.FieldDeclaration.class);
        add(com.github.javaparser.ast.body.InitializerDeclaration.class);
        add(com.github.javaparser.ast.body.MethodDeclaration.class);
        add(com.github.javaparser.ast.body.Parameter.class);
        add(com.github.javaparser.ast.body.ReceiverParameter.class);
        add(com.github.javaparser.ast.body.RecordDeclaration.class);
        add(CompactConstructorDeclaration.class);
        add(com.github.javaparser.ast.body.VariableDeclarator.class);

        add(com.github.javaparser.ast.comments.Comment.class); // First, as it is the base of other comment types
        add(com.github.javaparser.ast.comments.BlockComment.class);
        add(com.github.javaparser.ast.comments.JavadocComment.class);
        add(com.github.javaparser.ast.comments.LineComment.class);

        add(com.github.javaparser.ast.expr.ArrayAccessExpr.class);
        add(com.github.javaparser.ast.expr.ArrayCreationExpr.class);
        add(com.github.javaparser.ast.expr.ArrayInitializerExpr.class);
        add(com.github.javaparser.ast.expr.AssignExpr.class);
        add(com.github.javaparser.ast.expr.BinaryExpr.class);
        add(com.github.javaparser.ast.expr.BooleanLiteralExpr.class);
        add(com.github.javaparser.ast.expr.CastExpr.class);
        add(com.github.javaparser.ast.expr.CharLiteralExpr.class);
        add(com.github.javaparser.ast.expr.ClassExpr.class);
        add(com.github.javaparser.ast.expr.ConditionalExpr.class);
        add(com.github.javaparser.ast.expr.DoubleLiteralExpr.class);
        add(com.github.javaparser.ast.expr.EnclosedExpr.class);
        add(com.github.javaparser.ast.expr.FieldAccessExpr.class);
        add(com.github.javaparser.ast.expr.InstanceOfExpr.class);
        add(com.github.javaparser.ast.expr.IntegerLiteralExpr.class);
        add(com.github.javaparser.ast.expr.LambdaExpr.class);
        add(com.github.javaparser.ast.expr.LongLiteralExpr.class);
        add(com.github.javaparser.ast.expr.MarkerAnnotationExpr.class);
        add(com.github.javaparser.ast.expr.MemberValuePair.class);
        add(com.github.javaparser.ast.expr.MethodCallExpr.class);
        add(com.github.javaparser.ast.expr.MethodReferenceExpr.class);
        add(com.github.javaparser.ast.expr.NameExpr.class);
        add(com.github.javaparser.ast.expr.Name.class);
        add(com.github.javaparser.ast.expr.NormalAnnotationExpr.class);
        add(com.github.javaparser.ast.expr.NullLiteralExpr.class);
        add(com.github.javaparser.ast.expr.ObjectCreationExpr.class);
        add(com.github.javaparser.ast.expr.PatternExpr.class);
        add(com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class);
        add(com.github.javaparser.ast.expr.SimpleName.class);
        add(com.github.javaparser.ast.expr.SuperExpr.class);
        add(com.github.javaparser.ast.expr.SwitchExpr.class);
        add(com.github.javaparser.ast.expr.TextBlockLiteralExpr.class);
        add(com.github.javaparser.ast.expr.ThisExpr.class);
        add(com.github.javaparser.ast.expr.TypeExpr.class);
        add(com.github.javaparser.ast.expr.UnaryExpr.class);
        add(com.github.javaparser.ast.expr.VariableDeclarationExpr.class);

        add(com.github.javaparser.ast.stmt.AssertStmt.class);
        add(com.github.javaparser.ast.stmt.BlockStmt.class);
        add(com.github.javaparser.ast.stmt.BreakStmt.class);
        add(com.github.javaparser.ast.stmt.CatchClause.class);
        add(com.github.javaparser.ast.stmt.ContinueStmt.class);
        add(com.github.javaparser.ast.stmt.DoStmt.class);
        add(com.github.javaparser.ast.stmt.EmptyStmt.class);
        add(com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt.class);
        add(com.github.javaparser.ast.stmt.ExpressionStmt.class);
        add(com.github.javaparser.ast.stmt.ForEachStmt.class);
        add(com.github.javaparser.ast.stmt.ForStmt.class);
        add(com.github.javaparser.ast.stmt.IfStmt.class);
        add(com.github.javaparser.ast.stmt.LabeledStmt.class);
        add(com.github.javaparser.ast.stmt.LocalClassDeclarationStmt.class);
        add(com.github.javaparser.ast.stmt.LocalRecordDeclarationStmt.class);
        add(com.github.javaparser.ast.stmt.ReturnStmt.class);
        add(com.github.javaparser.ast.stmt.SwitchEntry.class);
        add(com.github.javaparser.ast.stmt.SwitchStmt.class);
        add(com.github.javaparser.ast.stmt.SynchronizedStmt.class);
        add(com.github.javaparser.ast.stmt.ThrowStmt.class);
        add(com.github.javaparser.ast.stmt.TryStmt.class);
        add(com.github.javaparser.ast.stmt.UnparsableStmt.class);
        add(com.github.javaparser.ast.stmt.WhileStmt.class);
        add(com.github.javaparser.ast.stmt.YieldStmt.class);

        add(com.github.javaparser.ast.type.ArrayType.class);
        add(com.github.javaparser.ast.type.ClassOrInterfaceType.class);
        add(com.github.javaparser.ast.type.IntersectionType.class);
        add(com.github.javaparser.ast.type.PrimitiveType.class);
        add(com.github.javaparser.ast.type.TypeParameter.class);
        add(com.github.javaparser.ast.type.UnionType.class);
        add(com.github.javaparser.ast.type.UnknownType.class);
        add(com.github.javaparser.ast.type.VarType.class);
        add(com.github.javaparser.ast.type.VoidType.class);
        add(com.github.javaparser.ast.type.WildcardType.class);

        add(com.github.javaparser.ast.modules.ModuleExportsDirective.class);
        add(com.github.javaparser.ast.modules.ModuleOpensDirective.class);
        add(com.github.javaparser.ast.modules.ModuleProvidesDirective.class);
        add(com.github.javaparser.ast.modules.ModuleRequiresDirective.class);
        add(com.github.javaparser.ast.modules.ModuleUsesDirective.class);
    }};

    public MetaModelGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new RuntimeException("Need 1 parameter: the JavaParser source checkout root directory.");
        }
        final Path root = Paths.get(args[0], "..", "javaparser-core", "src", "main", "java");
        final ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.RAW)
                .setStoreTokens(false);
        final SourceRoot sourceRoot = new SourceRoot(root, parserConfiguration);
        PrinterConfiguration config = new DefaultPrinterConfiguration().addOption(new DefaultConfigurationOption(ConfigOption.END_OF_LINE_CHARACTER, ("\n")));
        Printer printer = new DefaultPrettyPrinter(config);
        sourceRoot.setPrinter(printer::print);
        StaticJavaParser.setConfiguration(parserConfiguration);

        new MetaModelGenerator(sourceRoot).generate();

        sourceRoot.saveAll();
    }

    public void generate() throws Exception {
        final CompilationUnit javaParserMetaModelCu = sourceRoot.parse(METAMODEL_PACKAGE, "JavaParserMetaModel.java");
        javaParserMetaModelCu.setBlockComment(COPYRIGHT_NOTICE_JP_CORE);

        generateNodeMetaModels(javaParserMetaModelCu, sourceRoot);
    }

    private void generateNodeMetaModels(CompilationUnit javaParserMetaModelCu, SourceRoot sourceRoot) throws NoSuchMethodException {
        final ClassOrInterfaceDeclaration metaModelCoid = javaParserMetaModelCu.getClassByName("JavaParserMetaModel").get();

        // Initialiser methods
        final MethodDeclaration initializeNodeMetaModelsMethod = metaModelCoid.getMethodsByName("initializeNodeMetaModels").get(0);
        final MethodDeclaration initializePropertyMetaModelsMethod = metaModelCoid.getMethodsByName("initializePropertyMetaModels").get(0);
        final MethodDeclaration initializeConstructorParametersVariable = metaModelCoid.getMethodsByName("initializeConstructorParameters").get(0);

        // Ensure annotation `@Generated` is added to indicate the contents of each are generated.
        annotateGenerated(initializeNodeMetaModelsMethod);
        annotateGenerated(initializePropertyMetaModelsMethod);
        annotateGenerated(initializeConstructorParametersVariable);

        // Empty the body of the initialiser methods, to be (re-)generated below.
        final NodeList<Statement> initializeNodeMetaModelsStatements = initializeNodeMetaModelsMethod.getBody().get().getStatements();
        final NodeList<Statement> initializePropertyMetaModelsStatements = initializePropertyMetaModelsMethod.getBody().get().getStatements();
        final NodeList<Statement> initializeConstructorParametersStatements = initializeConstructorParametersVariable.getBody().get().getStatements();
        initializeNodeMetaModelsStatements.clear();
        initializePropertyMetaModelsStatements.clear();
        initializeConstructorParametersStatements.clear();

        // Remove fields, to be (re-)generated  below.
        metaModelCoid.getFields().stream()
                .filter(f -> f.getVariable(0).getNameAsString().endsWith("MetaModel"))
                .forEach(Node::remove);

        // Do the generation of each node metamodel class.
        final NodeMetaModelGenerator nodeMetaModelGenerator = new NodeMetaModelGenerator(sourceRoot);
        for (Class<? extends Node> nodeClass : ALL_NODE_CLASSES) {
            nodeMetaModelGenerator.generate(
                    nodeClass,
                    metaModelCoid,
                    initializeNodeMetaModelsStatements,
                    initializePropertyMetaModelsStatements,
                    initializeConstructorParametersStatements,
                    sourceRoot
            );
        }

        // TODO: Document why sorting occurs.
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
