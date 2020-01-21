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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.metamodel.DerivedProperty;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.utils.SourceRoot;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.ast.Modifier.Keyword.*;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.*;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.CodeGenerationUtils.optionalOf;
import static com.github.javaparser.utils.Utils.decapitalize;

public class NodeMetaModelGenerator {
    private static final String COPYRIGHT_NOTICE = "\n" +
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

    private final InitializePropertyMetaModelsStatementsGenerator initializePropertyMetaModelsStatementsGenerator = new InitializePropertyMetaModelsStatementsGenerator();
    private final InitializeConstructorParametersStatementsGenerator initializeConstructorParametersStatementsGenerator = new InitializeConstructorParametersStatementsGenerator();

    public void generate(Class<? extends Node> nodeClass, ClassOrInterfaceDeclaration metaModelCoid, NodeList<Statement> initializeNodeMetaModelsStatements, NodeList<Statement> initializePropertyMetaModelsStatements, NodeList<Statement> initializeConstructorParametersStatements, SourceRoot sourceRoot) throws NoSuchMethodException {
        final String className = nodeMetaModelName(nodeClass);
        final String nodeMetaModelFieldName = decapitalize(className);
        metaModelCoid.getFieldByName(nodeMetaModelFieldName).ifPresent(Node::remove);

        final FieldDeclaration nodeField = metaModelCoid.addField(className, nodeMetaModelFieldName, PUBLIC, STATIC, FINAL);

        final Class<?> superclass = nodeClass.getSuperclass();
        final String superNodeMetaModel = nodeMetaModelName(superclass);

        boolean isRootNode = !isNode(superclass);
        nodeField.getVariable(0).setInitializer(parseExpression(f("new %s(%s)",
                className,
                optionalOf(decapitalize(superNodeMetaModel), !isRootNode))));

        initializeNodeMetaModelsStatements.add(parseStatement(f("nodeMetaModels.add(%s);", nodeMetaModelFieldName)));

        final CompilationUnit classMetaModelJavaFile = new CompilationUnit(METAMODEL_PACKAGE);
        classMetaModelJavaFile.setBlockComment(COPYRIGHT_NOTICE);
        classMetaModelJavaFile.addImport("java.util.Optional");
        sourceRoot.add(METAMODEL_PACKAGE, className + ".java", classMetaModelJavaFile);
        final ClassOrInterfaceDeclaration nodeMetaModelClass = classMetaModelJavaFile.addClass(className, PUBLIC);
        if (isRootNode) {
            nodeMetaModelClass.addExtendedType(BASE_NODE_META_MODEL);
        } else {
            nodeMetaModelClass.addExtendedType(superNodeMetaModel);
        }

        final AstTypeAnalysis typeAnalysis = new AstTypeAnalysis(nodeClass);

        final ConstructorDeclaration classMMConstructor = nodeMetaModelClass
                .addConstructor()
                .addParameter("Optional<" + BASE_NODE_META_MODEL + ">", "super" + BASE_NODE_META_MODEL);
        classMMConstructor
                .getBody()
                .addStatement(parseExplicitConstructorInvocationStmt(f("super(super%s, %s.class, \"%s\", \"%s\", %s, %s);",
                        BASE_NODE_META_MODEL,
                        nodeClass.getName(),
                        nodeClass.getSimpleName(),
                        nodeClass.getPackage().getName(),
                        typeAnalysis.isAbstract,
                        typeAnalysis.isSelfType)));

        if (typeAnalysis.isAbstract) {
            classMetaModelJavaFile.addImport(Node.class);
            nodeMetaModelClass.addMember(parseBodyDeclaration(f(
                    "protected %s(Optional<BaseNodeMetaModel> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {" +
                            "super(superNodeMetaModel, type, name, packageName, isAbstract, hasWildcard);" +
                            " }",
                    className)));
        }

        final List<Field> fields = new ArrayList<>(Arrays.asList(nodeClass.getDeclaredFields()));
        fields.sort(Comparator.comparing(Field::getName));
        for (Field field : fields) {
            if (fieldShouldBeIgnored(field)) {
                continue;
            }

            initializePropertyMetaModelsStatementsGenerator.generate(field, nodeMetaModelClass, nodeMetaModelFieldName, initializePropertyMetaModelsStatements);
        }
        final List<Method> methods = new ArrayList<>(Arrays.asList(nodeClass.getMethods()));
        methods.sort(Comparator.comparing(Method::getName));
        for (Method method : methods) {
            if (method.isAnnotationPresent(DerivedProperty.class)) {
                initializePropertyMetaModelsStatementsGenerator.generateDerivedProperty(method, nodeMetaModelClass, nodeMetaModelFieldName, initializePropertyMetaModelsStatements);
            }
        }

        initializeConstructorParametersStatementsGenerator.generate(nodeClass, initializeConstructorParametersStatements);

        moveStaticInitializeToTheEndOfTheClassBecauseWeNeedTheFieldsToInitializeFirst(metaModelCoid);
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
