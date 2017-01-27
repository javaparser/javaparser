package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.stmt.Statement;

import java.lang.reflect.Field;

import static com.github.javaparser.JavaParser.parseStatement;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.isNode;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.nodeMetaModelName;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

public class InitializePropertyMetaModelsStatementsGenerator {
    public void generate(Class<?> nodeClass, Field field, ClassOrInterfaceDeclaration nodeMetaModelClass, String nodeMetaModelFieldName, NodeList<Statement> initializePropertyMetaModelsStatements) throws NoSuchMethodException {

        AstTypeAnalysis fieldAnalysis = new AstTypeAnalysis(nodeClass.getMethod(getter(field)).getGenericReturnType());

        Class<?> fieldType = fieldAnalysis.innerType;
        String typeName = fieldType.getTypeName().replace('$', '.');
        String propertyMetaModelFieldName = field.getName() + "PropertyMetaModel";
        nodeMetaModelClass.addField("PropertyMetaModel", propertyMetaModelFieldName, PUBLIC);
        String propertyInitializer = f("new PropertyMetaModel(%s, \"%s\", %s.class, %s, %s, %s, %s, %s)",
                nodeMetaModelFieldName,
                field.getName(),
                typeName,
                optionalOf(decapitalize(nodeMetaModelName(fieldType)), isNode(fieldType)),
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

}
