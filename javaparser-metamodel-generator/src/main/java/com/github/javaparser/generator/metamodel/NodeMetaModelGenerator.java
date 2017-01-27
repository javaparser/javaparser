package com.github.javaparser.generator.metamodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.generator.utils.SourceRoot;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.ast.Modifier.FINAL;
import static com.github.javaparser.ast.Modifier.PUBLIC;
import static com.github.javaparser.generator.metamodel.MetaModelGenerator.*;
import static com.github.javaparser.generator.utils.GeneratorUtils.*;

public class NodeMetaModelGenerator {
    private final PropertyMetaModelGenerator propertyMetaModelGenerator = new PropertyMetaModelGenerator();

    public void generate(Class<? extends Node> c, ClassOrInterfaceDeclaration mmClass, NodeList<Statement> initializeNodeMetaModelsStatements, NodeList<Statement> initializePropertyMetaModelsStatements, NodeList<Statement> initializeConstructorParametersStatements, SourceRoot sourceRoot) throws NoSuchMethodException {
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

        List<Field> fields = new ArrayList<>(Arrays.asList(c.getDeclaredFields()));
        fields.sort(Comparator.comparing(Field::getName));
        for (Field field : fields) {
            if (fieldShouldBeIgnored(field)) {
                continue;
            }

            propertyMetaModelGenerator.generate(c, field, classMetaModelClass, fieldName, initializePropertyMetaModelsStatements, initializeConstructorParametersStatements);
        }
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
            case "commentedNode":
            case "orphanComments":
                return true;
        }
        return false;
    }

}
