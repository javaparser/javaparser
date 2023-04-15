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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.generator.AbstractGenerator;
import com.github.javaparser.metamodel.DerivedProperty;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.utils.SourceRoot;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.*;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.ast.Modifier.Keyword.*;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.CodeGenerationUtils.optionalOf;
import static com.github.javaparser.utils.Utils.decapitalize;

public class NodeMetaModelGenerator extends AbstractGenerator {

    private final InitializePropertyMetaModelsStatementsGenerator initializePropertyMetaModelsStatementsGenerator = new InitializePropertyMetaModelsStatementsGenerator();
    private final InitializeConstructorParametersStatementsGenerator initializeConstructorParametersStatementsGenerator = new InitializeConstructorParametersStatementsGenerator();

    public static final String GENERATED_CLASS_COMMENT = "" +
            "This file, class, and its contents are completely generated based on:" +
            "\n<ul>" +
            "\n    <li>The contents and annotations within the package `com.github.javaparser.ast`, and</li>" +
            "\n    <li>`ALL_NODE_CLASSES` within the class `com.github.javaparser.generator.metamodel.MetaModelGenerator`.</li>" +
            "\n</ul>" +
            "\n" +
            "\nFor this reason, any changes made directly to this file will be overwritten the next time generators are run." +
            "";

    private static final String GENERATED_JAVADOC_COMMENT = "Warning: The content of this class is partially or completely generated - manual edits risk being overwritten.";

    protected NodeMetaModelGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    public void generate(Class<? extends Node> nodeClass, ClassOrInterfaceDeclaration metaModelCoid, NodeList<Statement> initializeNodeMetaModelsStatements, NodeList<Statement> initializePropertyMetaModelsStatements, NodeList<Statement> initializeConstructorParametersStatements, SourceRoot sourceRoot) throws NoSuchMethodException {
        metaModelCoid.setJavadocComment(GENERATED_JAVADOC_COMMENT);

        final AstTypeAnalysis typeAnalysis = new AstTypeAnalysis(nodeClass);

        final String className = MetaModelGenerator.nodeMetaModelName(nodeClass);
        final String nodeMetaModelFieldName = decapitalize(className);
        metaModelCoid.getFieldByName(nodeMetaModelFieldName).ifPresent(Node::remove);

        initializeNodeMetaModelsStatements.add(parseStatement(f("nodeMetaModels.add(%s);", nodeMetaModelFieldName)));
        this.initializeConstructorParametersStatementsGenerator.generate(nodeClass, initializeConstructorParametersStatements);

        final Class<?> superclass = nodeClass.getSuperclass();
        final String superNodeMetaModel = MetaModelGenerator.nodeMetaModelName(superclass);
        final boolean isRootNode = !MetaModelGenerator.isNode(superclass);

        final FieldDeclaration nodeField = metaModelCoid.addField(className, nodeMetaModelFieldName, PUBLIC, STATIC, FINAL);
        annotateGenerated(nodeField);
        nodeField.getVariable(0).setInitializer(
                parseExpression(
                        f("new %s(%s)",
                                className,
                                optionalOf(decapitalize(superNodeMetaModel), !isRootNode))
                )
        );


        // The node-specific metamodel file
        final CompilationUnit classMetaModelJavaFile = new CompilationUnit(MetaModelGenerator.METAMODEL_PACKAGE);
        classMetaModelJavaFile.setBlockComment(COPYRIGHT_NOTICE_JP_CORE);
        classMetaModelJavaFile.addImport(Optional.class);
        classMetaModelJavaFile.addImport(nodeClass);

        //
        final ClassOrInterfaceDeclaration nodeMetaModelClass = classMetaModelJavaFile.addClass(className, PUBLIC);
        annotateGenerated(nodeMetaModelClass);
        nodeMetaModelClass.setJavadocComment(GENERATED_CLASS_COMMENT);

        if (isRootNode) {
            nodeMetaModelClass.addExtendedType(MetaModelGenerator.BASE_NODE_META_MODEL);
        } else {
            nodeMetaModelClass.addExtendedType(superNodeMetaModel);
        }

        // Constructors
        final ConstructorDeclaration classMMConstructor = nodeMetaModelClass
                .addConstructor()
                .addParameter(
                        f("Optional<%s>", MetaModelGenerator.BASE_NODE_META_MODEL),
                        f("super%s", MetaModelGenerator.BASE_NODE_META_MODEL)
                );
        classMMConstructor
                .getBody()
                .addStatement(
                        parseExplicitConstructorInvocationStmt(f("super(super%s, %s.class, \"%s\", \"%s\", %s, %s);",
                                MetaModelGenerator.BASE_NODE_META_MODEL,
                                nodeClass.getSimpleName(),
                                nodeClass.getSimpleName(),
                                nodeClass.getPackage().getName(),
                                typeAnalysis.isAbstract,
                                typeAnalysis.isSelfType
                        ))
                );
        annotateGenerated(classMMConstructor);

        // ?Abstract protected constructor?
        if (typeAnalysis.isAbstract) {
            classMetaModelJavaFile.addImport(Node.class);
            BodyDeclaration<?> bodyDeclaration = parseBodyDeclaration(f(
                    "protected %s(Optional<%s> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {" +
                            "super(superNodeMetaModel, type, name, packageName, isAbstract, hasWildcard);" +
                            " }",
                    className,
                    MetaModelGenerator.BASE_NODE_META_MODEL
            ));
            annotateGenerated(bodyDeclaration);
            nodeMetaModelClass.addMember(bodyDeclaration);
        }

        // Fields, sorted by name.
        final List<Field> fields = new ArrayList<>(Arrays.asList(nodeClass.getDeclaredFields()));
        fields.sort(Comparator.comparing(Field::getName));
        for (Field field : fields) {
            if (this.fieldShouldBeIgnored(field)) {
                continue;
            }

            this.initializePropertyMetaModelsStatementsGenerator.generate(field, nodeMetaModelClass, nodeMetaModelFieldName, initializePropertyMetaModelsStatements);
        }

        // Methods, sorted by name.
        final List<Method> methods = new ArrayList<>(Arrays.asList(nodeClass.getMethods()));
        methods.sort(Comparator.comparing(Method::getName));
        for (Method method : methods) {
            if (method.isAnnotationPresent(DerivedProperty.class)) {
                this.initializePropertyMetaModelsStatementsGenerator.generateDerivedProperty(method, nodeMetaModelClass, nodeMetaModelFieldName, initializePropertyMetaModelsStatements);
            }
        }


        this.moveStaticInitializeToTheEndOfTheClassBecauseWeNeedTheFieldsToInitializeFirst(metaModelCoid);

        // Add the file to the source root, enabling it to be saved later.
        sourceRoot.add(MetaModelGenerator.METAMODEL_PACKAGE, className + ".java", classMetaModelJavaFile);
    }

    private void moveStaticInitializeToTheEndOfTheClassBecauseWeNeedTheFieldsToInitializeFirst(ClassOrInterfaceDeclaration metaModelCoid) {
        for (BodyDeclaration<?> m : metaModelCoid.getMembers()) {
            if (m instanceof InitializerDeclaration) {
                m.remove();
                metaModelCoid.addMember(m);
                return;
            }
        }
    }

    private boolean fieldShouldBeIgnored(Field reflectionField) {
        return java.lang.reflect.Modifier.isStatic(reflectionField.getModifiers()) ||
                reflectionField.isAnnotationPresent(InternalProperty.class);
    }
}
