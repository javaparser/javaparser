package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.stmt.Statement;

import java.lang.reflect.Field;

import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.isNode;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.nodeMetaModelName;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

public class InitializePropertyMetaModelsStatementsGenerator {
    public void generate(Class<?> nodeClass, Field field, ClassOrInterfaceDeclaration nodeMetaModelClass, String nodeMetaModelFieldName, NodeList<Statement> initializePropertyMetaModelsStatements) throws NoSuchMethodException {

        final AstTypeAnalysis fieldAnalysis = new AstTypeAnalysis(nodeClass.getMethod(getter(field)).getGenericReturnType());

        final Class<?> fieldType = fieldAnalysis.innerType;
        final String typeName = fieldType.getTypeName().replace('$', '.');
        final String propertyMetaModelFieldName = field.getName() + "PropertyMetaModel";
        nodeMetaModelClass.addField("PropertyMetaModel", propertyMetaModelFieldName, PUBLIC);
        final String propertyInitializer = f("new PropertyMetaModel(%s, \"%s\", %s.class, %s, %s, %s, %s, %s, %s)",
                nodeMetaModelFieldName,
                field.getName(),
                typeName,
                optionalOf(decapitalize(nodeMetaModelName(fieldType)), isNode(fieldType)),
                fieldAnalysis.isOptional,
                isNonEmpty(field),
                fieldAnalysis.isNodeList,
                fieldAnalysis.isEnumSet,
                fieldAnalysis.isSelfType);
        final String fieldSetting = f("%s.%s=%s;", nodeMetaModelFieldName, propertyMetaModelFieldName, propertyInitializer);
        final String fieldAddition = f("%s.getDeclaredPropertyMetaModels().add(%s.%s);", nodeMetaModelFieldName, nodeMetaModelFieldName, propertyMetaModelFieldName);

        initializePropertyMetaModelsStatements.add(parseStatement(fieldSetting));
        initializePropertyMetaModelsStatements.add(parseStatement(fieldAddition));
    }

    private boolean isNonEmpty(Field field) {
        final String name = field.getName();
        final Class<?> c = field.getDeclaringClass();
        return (c == VariableDeclarator.class && name.equals("initializer")) ||
                (c == MethodReferenceExpr.class && name.equals("identifier")) ||
                (c == Name.class && name.equals("identifier")) ||
                (c == SimpleName.class && name.equals("identifier"));
    }

    private String getter(Field field) {
        return getterName(field.getType(), field.getName());
    }

}
