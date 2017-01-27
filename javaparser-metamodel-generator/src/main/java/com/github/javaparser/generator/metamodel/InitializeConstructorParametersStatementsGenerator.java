package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.stmt.Statement;

import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;

import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.isNode;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.metaModelName;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

public class InitializeConstructorParametersStatementsGenerator {
    public void generate2(Class<?> nodeClass, Field field, ClassOrInterfaceDeclaration nodeMetaModelClass, String nodeMetaModelFieldName, NodeList<Statement> initializePropertyMetaModelsStatements) throws NoSuchMethodException {

        AstTypeAnalysis fieldAnalysis = new AstTypeAnalysis(nodeClass.getMethod(getter(field)).getGenericReturnType());

        Class<?> fieldType = fieldAnalysis.innerType;
        String typeName = fieldType.getTypeName().replace('$', '.');
        String propertyMetaModelFieldName = field.getName() + "PropertyMetaModel";
        nodeMetaModelClass.addField("PropertyMetaModel", propertyMetaModelFieldName, PUBLIC);
        String propertyInitializer = f("new PropertyMetaModel(%s, \"%s\", %s.class, %s, %s, %s, %s, %s)",
                nodeMetaModelFieldName,
                field.getName(),
                typeName,
                optionalOf(decapitalize(metaModelName(fieldType)), isNode(fieldType)),
                fieldAnalysis.isOptional,
                fieldAnalysis.isNodeList,
                fieldAnalysis.isEnumSet,
                fieldAnalysis.isSelfType);
        String fieldSetting = f("%s.%s=%s;", nodeMetaModelFieldName, propertyMetaModelFieldName, propertyInitializer);
        String fieldAddition = f("%s.getDeclaredPropertyMetaModels().add(%s.%s);", nodeMetaModelFieldName, nodeMetaModelFieldName, propertyMetaModelFieldName);

        initializePropertyMetaModelsStatements.add(parseStatement(fieldSetting));
        initializePropertyMetaModelsStatements.add(parseStatement(fieldAddition));
    }

    private String getter(Field field) {
        return getterName(field.getType(), field.getName());
    }

    public void generate(Class<? extends Node> nodeClass, NodeList<Statement> initializeConstructorParametersStatements) {
        Constructor<?> constructor = findAllFieldsConstructor(nodeClass);
        for (java.lang.reflect.Parameter parameter : constructor.getParameters()) {
            Field field = findFieldInClass(nodeClass, parameter.getName());
            
        }
    }

    private Field findFieldInClass(Class<?> nodeClass, String name) {
        do {
            for (Field field : nodeClass.getDeclaredFields()) {
                if (field.getName().equals(name)) {
                    return field;
                }
            }
            nodeClass = nodeClass.getSuperclass();
        } while (nodeClass != null);
        throw new AssertionError(f("Couldn't find constructor parameter %s as a field", name));
    }

    private Constructor<?> findAllFieldsConstructor(Class<? extends Node> nodeClass) {
        for (Constructor<?> constructor : nodeClass.getDeclaredConstructors()) {
            for (Annotation annotation : constructor.getAnnotations()) {
                if (annotation.annotationType() == AllFieldsConstructor.class) {
                    return constructor;
                }
            }
        }
        throw new AssertionError(f("Node class %s has no constructor annotated with @AllFieldsConstructor", nodeClass.getSimpleName()));
    }
}
