package com.github.javaparser.metamodel;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The model contains meta-data about all nodes in the AST.
 * You can base source code generators on it.
 */
public class JavaParserMetaModel {

    public final List<BaseNodeMetaModel> classMetaModels = new ArrayList<>();

    public JavaParserMetaModel() {
        initializeClassMetaModels();
        initializeFieldMetaModels();
    }

    private void initializeClassMetaModels() {
        classMetaModels.add(annotationDeclarationMetaModel);
        classMetaModels.add(annotationExprMetaModel);
        classMetaModels.add(annotationMemberDeclarationMetaModel);
        classMetaModels.add(arrayAccessExprMetaModel);
        classMetaModels.add(arrayCreationExprMetaModel);
        classMetaModels.add(arrayCreationLevelMetaModel);
        classMetaModels.add(arrayInitializerExprMetaModel);
        classMetaModels.add(arrayTypeMetaModel);
        classMetaModels.add(assertStmtMetaModel);
        classMetaModels.add(assignExprMetaModel);
        classMetaModels.add(binaryExprMetaModel);
        classMetaModels.add(blockCommentMetaModel);
        classMetaModels.add(blockStmtMetaModel);
        classMetaModels.add(bodyDeclarationMetaModel);
        classMetaModels.add(booleanLiteralExprMetaModel);
        classMetaModels.add(breakStmtMetaModel);
        classMetaModels.add(castExprMetaModel);
        classMetaModels.add(catchClauseMetaModel);
        classMetaModels.add(charLiteralExprMetaModel);
        classMetaModels.add(classExprMetaModel);
        classMetaModels.add(classOrInterfaceDeclarationMetaModel);
        classMetaModels.add(classOrInterfaceTypeMetaModel);
        classMetaModels.add(commentMetaModel);
        classMetaModels.add(compilationUnitMetaModel);
        classMetaModels.add(conditionalExprMetaModel);
        classMetaModels.add(constructorDeclarationMetaModel);
        classMetaModels.add(continueStmtMetaModel);
        classMetaModels.add(doStmtMetaModel);
        classMetaModels.add(doubleLiteralExprMetaModel);
        classMetaModels.add(emptyMemberDeclarationMetaModel);
        classMetaModels.add(emptyStmtMetaModel);
        classMetaModels.add(enclosedExprMetaModel);
        classMetaModels.add(enumConstantDeclarationMetaModel);
        classMetaModels.add(enumDeclarationMetaModel);
        classMetaModels.add(explicitConstructorInvocationStmtMetaModel);
        classMetaModels.add(expressionMetaModel);
        classMetaModels.add(expressionStmtMetaModel);
        classMetaModels.add(fieldAccessExprMetaModel);
        classMetaModels.add(fieldDeclarationMetaModel);
        classMetaModels.add(forStmtMetaModel);
        classMetaModels.add(foreachStmtMetaModel);
        classMetaModels.add(ifStmtMetaModel);
        classMetaModels.add(importDeclarationMetaModel);
        classMetaModels.add(initializerDeclarationMetaModel);
        classMetaModels.add(instanceOfExprMetaModel);
        classMetaModels.add(integerLiteralExprMetaModel);
        classMetaModels.add(intersectionTypeMetaModel);
        classMetaModels.add(javadocCommentMetaModel);
        classMetaModels.add(labeledStmtMetaModel);
        classMetaModels.add(lambdaExprMetaModel);
        classMetaModels.add(lineCommentMetaModel);
        classMetaModels.add(literalExprMetaModel);
        classMetaModels.add(localClassDeclarationStmtMetaModel);
        classMetaModels.add(longLiteralExprMetaModel);
        classMetaModels.add(markerAnnotationExprMetaModel);
        classMetaModels.add(memberValuePairMetaModel);
        classMetaModels.add(methodCallExprMetaModel);
        classMetaModels.add(methodDeclarationMetaModel);
        classMetaModels.add(methodReferenceExprMetaModel);
        classMetaModels.add(nameExprMetaModel);
        classMetaModels.add(nameMetaModel);
        classMetaModels.add(nodeListMetaModel);
        classMetaModels.add(nodeMetaModel);
        classMetaModels.add(normalAnnotationExprMetaModel);
        classMetaModels.add(nullLiteralExprMetaModel);
        classMetaModels.add(objectCreationExprMetaModel);
        classMetaModels.add(packageDeclarationMetaModel);
        classMetaModels.add(parameterMetaModel);
        classMetaModels.add(primitiveTypeMetaModel);
        classMetaModels.add(referenceTypeMetaModel);
        classMetaModels.add(returnStmtMetaModel);
        classMetaModels.add(simpleNameMetaModel);
        classMetaModels.add(singleMemberAnnotationExprMetaModel);
        classMetaModels.add(statementMetaModel);
        classMetaModels.add(stringLiteralExprMetaModel);
        classMetaModels.add(superExprMetaModel);
        classMetaModels.add(switchEntryStmtMetaModel);
        classMetaModels.add(switchStmtMetaModel);
        classMetaModels.add(synchronizedStmtMetaModel);
        classMetaModels.add(thisExprMetaModel);
        classMetaModels.add(throwStmtMetaModel);
        classMetaModels.add(tryStmtMetaModel);
        classMetaModels.add(typeDeclarationMetaModel);
        classMetaModels.add(typeExprMetaModel);
        classMetaModels.add(typeMetaModel);
        classMetaModels.add(typeParameterMetaModel);
        classMetaModels.add(unaryExprMetaModel);
        classMetaModels.add(unionTypeMetaModel);
        classMetaModels.add(unknownTypeMetaModel);
        classMetaModels.add(variableDeclarationExprMetaModel);
        classMetaModels.add(variableDeclaratorMetaModel);
        classMetaModels.add(voidTypeMetaModel);
        classMetaModels.add(whileStmtMetaModel);
        classMetaModels.add(wildcardTypeMetaModel);
    }

    private void initializeFieldMetaModels() {
        nodeMetaModel.propertyMetaModels.add(new PropertyMetaModel(nodeMetaModel, "getComment", "setComment", "comment", com.github.javaparser.ast.comments.Comment.class, getField(Node.class, "comment"), true, false, false, false, false));
        bodyDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(bodyDeclarationMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(BodyDeclaration.class, "annotations"), true, false, true, false, false));
        typeMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Type.class, "annotations"), true, false, true, false, false));
        annotationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(annotationExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(AnnotationExpr.class, "name"), true, false, false, false, false));
        typeDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeDeclarationMetaModel, "getMembers", "setMembers", "members", com.github.javaparser.ast.body.BodyDeclaration.class, getField(TypeDeclaration.class, "members"), true, false, true, false, true));
        typeDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(TypeDeclaration.class, "modifiers"), true, false, false, true, false));
        typeDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeDeclaration.class, "name"), true, false, false, false, false));
        stringLiteralExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(stringLiteralExprMetaModel, "getValue", "setValue", "value", java.lang.String.class, getField(StringLiteralExpr.class, "value"), true, false, false, false, false));
        arrayCreationLevelMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayCreationLevelMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(ArrayCreationLevel.class, "annotations"), true, false, true, false, false));
        arrayCreationLevelMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayCreationLevelMetaModel, "getDimension", "setDimension", "dimension", com.github.javaparser.ast.expr.Expression.class, getField(ArrayCreationLevel.class, "dimension"), true, true, false, false, false));
        compilationUnitMetaModel.propertyMetaModels.add(new PropertyMetaModel(compilationUnitMetaModel, "getImports", "setImports", "imports", com.github.javaparser.ast.ImportDeclaration.class, getField(CompilationUnit.class, "imports"), true, false, true, false, false));
        compilationUnitMetaModel.propertyMetaModels.add(new PropertyMetaModel(compilationUnitMetaModel, "getPackageDeclaration", "setPackageDeclaration", "packageDeclaration", com.github.javaparser.ast.PackageDeclaration.class, getField(CompilationUnit.class, "packageDeclaration"), true, true, false, false, false));
        compilationUnitMetaModel.propertyMetaModels.add(new PropertyMetaModel(compilationUnitMetaModel, "getTypes", "setTypes", "types", com.github.javaparser.ast.body.TypeDeclaration.class, getField(CompilationUnit.class, "types"), true, false, true, false, true));
        packageDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(packageDeclarationMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(PackageDeclaration.class, "annotations"), true, false, true, false, false));
        packageDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(packageDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(PackageDeclaration.class, "name"), true, false, false, false, false));
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(annotationMemberDeclarationMetaModel, "getDefaultValue", "setDefaultValue", "defaultValue", com.github.javaparser.ast.expr.Expression.class, getField(AnnotationMemberDeclaration.class, "defaultValue"), true, true, false, false, false));
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(annotationMemberDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(AnnotationMemberDeclaration.class, "modifiers"), true, false, false, true, false));
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(annotationMemberDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(AnnotationMemberDeclaration.class, "name"), true, false, false, false, false));
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(annotationMemberDeclarationMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(AnnotationMemberDeclaration.class, "type"), true, false, false, false, false));
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "extendedTypes"), true, false, true, false, false));
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "implementedTypes"), true, false, true, false, false));
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "isInterface", "setIsInterface", "isInterface", boolean.class, getField(ClassOrInterfaceDeclaration.class, "isInterface"), true, false, false, false, false));
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ClassOrInterfaceDeclaration.class, "typeParameters"), true, false, true, false, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(ConstructorDeclaration.class, "body"), true, false, false, false, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(ConstructorDeclaration.class, "modifiers"), true, false, false, true, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ConstructorDeclaration.class, "name"), true, false, false, false, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(ConstructorDeclaration.class, "parameters"), true, false, true, false, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(ConstructorDeclaration.class, "thrownExceptions"), true, false, true, false, false));
        constructorDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(constructorDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ConstructorDeclaration.class, "typeParameters"), true, false, true, false, false));
        enumConstantDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(enumConstantDeclarationMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(EnumConstantDeclaration.class, "arguments"), true, false, true, false, false));
        enumConstantDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(enumConstantDeclarationMetaModel, "getClassBody", "setClassBody", "classBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(EnumConstantDeclaration.class, "classBody"), true, false, true, false, true));
        enumConstantDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(enumConstantDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(EnumConstantDeclaration.class, "name"), true, false, false, false, false));
        enumDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(enumDeclarationMetaModel, "getEntries", "setEntries", "entries", com.github.javaparser.ast.body.EnumConstantDeclaration.class, getField(EnumDeclaration.class, "entries"), true, false, true, false, false));
        enumDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(enumDeclarationMetaModel, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(EnumDeclaration.class, "implementedTypes"), true, false, true, false, false));
        fieldDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(fieldDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(FieldDeclaration.class, "modifiers"), true, false, false, true, false));
        fieldDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(fieldDeclarationMetaModel, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(FieldDeclaration.class, "variables"), true, false, true, false, false));
        initializerDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(initializerDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(InitializerDeclaration.class, "body"), true, false, false, false, false));
        initializerDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(initializerDeclarationMetaModel, "isStatic", "setIsStatic", "isStatic", boolean.class, getField(InitializerDeclaration.class, "isStatic"), true, false, false, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(MethodDeclaration.class, "body"), true, true, false, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "isDefault", "setIsDefault", "isDefault", boolean.class, getField(MethodDeclaration.class, "isDefault"), true, false, false, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(MethodDeclaration.class, "modifiers"), true, false, false, true, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodDeclaration.class, "name"), true, false, false, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(MethodDeclaration.class, "parameters"), true, false, true, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(MethodDeclaration.class, "thrownExceptions"), true, false, true, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(MethodDeclaration.class, "type"), true, false, false, false, false));
        methodDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(MethodDeclaration.class, "typeParameters"), true, false, true, false, false));
        parameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(parameterMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Parameter.class, "annotations"), true, false, true, false, false));
        parameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(parameterMetaModel, "isVarArgs", "setIsVarArgs", "isVarArgs", boolean.class, getField(Parameter.class, "isVarArgs"), true, false, false, false, false));
        parameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(parameterMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(Parameter.class, "modifiers"), true, false, false, true, false));
        parameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(parameterMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(Parameter.class, "name"), true, false, false, false, false));
        parameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(parameterMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(Parameter.class, "type"), true, false, false, false, false));
        variableDeclaratorMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclaratorMetaModel, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.Expression.class, getField(VariableDeclarator.class, "initializer"), true, true, false, false, false));
        variableDeclaratorMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclaratorMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(VariableDeclarator.class, "name"), true, false, false, false, false));
        variableDeclaratorMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclaratorMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(VariableDeclarator.class, "type"), true, false, false, false, false));
        commentMetaModel.propertyMetaModels.add(new PropertyMetaModel(commentMetaModel, "getCommentedNode", "setCommentedNode", "commentedNode", com.github.javaparser.ast.Node.class, getField(Comment.class, "commentedNode"), true, true, false, false, false));
        commentMetaModel.propertyMetaModels.add(new PropertyMetaModel(commentMetaModel, "getContent", "setContent", "content", java.lang.String.class, getField(Comment.class, "content"), true, false, false, false, false));
        arrayAccessExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayAccessExprMetaModel, "getIndex", "setIndex", "index", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "index"), true, false, false, false, false));
        arrayAccessExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayAccessExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "name"), true, false, false, false, false));
        arrayCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayCreationExprMetaModel, "getElementType", "setElementType", "elementType", com.github.javaparser.ast.type.Type.class, getField(ArrayCreationExpr.class, "elementType"), true, false, false, false, false));
        arrayCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayCreationExprMetaModel, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.ArrayInitializerExpr.class, getField(ArrayCreationExpr.class, "initializer"), true, true, false, false, false));
        arrayCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayCreationExprMetaModel, "getLevels", "setLevels", "levels", com.github.javaparser.ast.ArrayCreationLevel.class, getField(ArrayCreationExpr.class, "levels"), true, false, true, false, false));
        arrayInitializerExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayInitializerExprMetaModel, "getValues", "setValues", "values", com.github.javaparser.ast.expr.Expression.class, getField(ArrayInitializerExpr.class, "values"), true, false, true, false, false));
        assignExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(assignExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.AssignExpr.Operator.class, getField(AssignExpr.class, "operator"), true, false, false, false, false));
        assignExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(assignExprMetaModel, "getTarget", "setTarget", "target", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "target"), true, false, false, false, false));
        assignExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(assignExprMetaModel, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "value"), true, false, false, false, false));
        binaryExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(binaryExprMetaModel, "getLeft", "setLeft", "left", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "left"), true, false, false, false, false));
        binaryExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(binaryExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.BinaryExpr.Operator.class, getField(BinaryExpr.class, "operator"), true, false, false, false, false));
        binaryExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(binaryExprMetaModel, "getRight", "setRight", "right", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "right"), true, false, false, false, false));
        booleanLiteralExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(booleanLiteralExprMetaModel, "getValue", "setValue", "value", boolean.class, getField(BooleanLiteralExpr.class, "value"), true, false, false, false, false));
        castExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(castExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(CastExpr.class, "expression"), true, false, false, false, false));
        castExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(castExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(CastExpr.class, "type"), true, false, false, false, false));
        classExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(classExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(ClassExpr.class, "type"), true, false, false, false, false));
        conditionalExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(conditionalExprMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "condition"), true, false, false, false, false));
        conditionalExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(conditionalExprMetaModel, "getElseExpr", "setElseExpr", "elseExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "elseExpr"), true, false, false, false, false));
        conditionalExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(conditionalExprMetaModel, "getThenExpr", "setThenExpr", "thenExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "thenExpr"), true, false, false, false, false));
        enclosedExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(enclosedExprMetaModel, "getInner", "setInner", "inner", com.github.javaparser.ast.expr.Expression.class, getField(EnclosedExpr.class, "inner"), true, true, false, false, false));
        fieldAccessExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(fieldAccessExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(FieldAccessExpr.class, "name"), true, false, false, false, false));
        fieldAccessExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(fieldAccessExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(FieldAccessExpr.class, "scope"), true, true, false, false, false));
        fieldAccessExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(fieldAccessExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(FieldAccessExpr.class, "typeArguments"), true, true, true, false, false));
        instanceOfExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(instanceOfExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(InstanceOfExpr.class, "expression"), true, false, false, false, false));
        instanceOfExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(instanceOfExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.ReferenceType.class, getField(InstanceOfExpr.class, "type"), true, false, false, false, false));
        lambdaExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(lambdaExprMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(LambdaExpr.class, "body"), true, false, false, false, false));
        lambdaExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(lambdaExprMetaModel, "isEnclosingParameters", "setIsEnclosingParameters", "isEnclosingParameters", boolean.class, getField(LambdaExpr.class, "isEnclosingParameters"), true, false, false, false, false));
        lambdaExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(lambdaExprMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(LambdaExpr.class, "parameters"), true, false, true, false, false));
        memberValuePairMetaModel.propertyMetaModels.add(new PropertyMetaModel(memberValuePairMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MemberValuePair.class, "name"), true, false, false, false, false));
        memberValuePairMetaModel.propertyMetaModels.add(new PropertyMetaModel(memberValuePairMetaModel, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField(MemberValuePair.class, "value"), true, false, false, false, false));
        methodCallExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodCallExprMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "arguments"), true, false, true, false, false));
        methodCallExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodCallExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodCallExpr.class, "name"), true, false, false, false, false));
        methodCallExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodCallExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "scope"), true, true, false, false, false));
        methodCallExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodCallExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodCallExpr.class, "typeArguments"), true, true, true, false, false));
        methodReferenceExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodReferenceExprMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(MethodReferenceExpr.class, "identifier"), true, false, false, false, false));
        methodReferenceExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodReferenceExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodReferenceExpr.class, "scope"), true, false, false, false, false));
        methodReferenceExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(methodReferenceExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodReferenceExpr.class, "typeArguments"), true, true, true, false, false));
        nameExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(nameExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(NameExpr.class, "name"), true, false, false, false, false));
        nameMetaModel.propertyMetaModels.add(new PropertyMetaModel(nameMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(Name.class, "identifier"), true, false, false, false, false));
        nameMetaModel.propertyMetaModels.add(new PropertyMetaModel(nameMetaModel, "getQualifier", "setQualifier", "qualifier", com.github.javaparser.ast.expr.Name.class, getField(Name.class, "qualifier"), true, true, false, false, false));
        normalAnnotationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(normalAnnotationExprMetaModel, "getPairs", "setPairs", "pairs", com.github.javaparser.ast.expr.MemberValuePair.class, getField(NormalAnnotationExpr.class, "pairs"), true, false, true, false, false));
        objectCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(objectCreationExprMetaModel, "getAnonymousClassBody", "setAnonymousClassBody", "anonymousClassBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(ObjectCreationExpr.class, "anonymousClassBody"), true, true, true, false, true));
        objectCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(objectCreationExprMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "arguments"), true, false, true, false, false));
        objectCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(objectCreationExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "scope"), true, true, false, false, false));
        objectCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(objectCreationExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ObjectCreationExpr.class, "type"), true, false, false, false, false));
        objectCreationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(objectCreationExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ObjectCreationExpr.class, "typeArguments"), true, true, true, false, false));
        simpleNameMetaModel.propertyMetaModels.add(new PropertyMetaModel(simpleNameMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(SimpleName.class, "identifier"), true, false, false, false, false));
        singleMemberAnnotationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(singleMemberAnnotationExprMetaModel, "getMemberValue", "setMemberValue", "memberValue", com.github.javaparser.ast.expr.Expression.class, getField(SingleMemberAnnotationExpr.class, "memberValue"), true, false, false, false, false));
        superExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(superExprMetaModel, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(SuperExpr.class, "classExpr"), true, true, false, false, false));
        thisExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(thisExprMetaModel, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(ThisExpr.class, "classExpr"), true, true, false, false, false));
        typeExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(TypeExpr.class, "type"), true, false, false, false, false));
        unaryExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(unaryExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(UnaryExpr.class, "expression"), true, false, false, false, false));
        unaryExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(unaryExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.UnaryExpr.Operator.class, getField(UnaryExpr.class, "operator"), true, false, false, false, false));
        variableDeclarationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclarationExprMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(VariableDeclarationExpr.class, "annotations"), true, false, true, false, false));
        variableDeclarationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclarationExprMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(VariableDeclarationExpr.class, "modifiers"), true, false, false, true, false));
        variableDeclarationExprMetaModel.propertyMetaModels.add(new PropertyMetaModel(variableDeclarationExprMetaModel, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(VariableDeclarationExpr.class, "variables"), true, false, true, false, false));
        importDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(importDeclarationMetaModel, "isAsterisk", "setIsAsterisk", "isAsterisk", boolean.class, getField(ImportDeclaration.class, "isAsterisk"), true, false, false, false, false));
        importDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(importDeclarationMetaModel, "isStatic", "setIsStatic", "isStatic", boolean.class, getField(ImportDeclaration.class, "isStatic"), true, false, false, false, false));
        importDeclarationMetaModel.propertyMetaModels.add(new PropertyMetaModel(importDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(ImportDeclaration.class, "name"), true, false, false, false, false));
        assertStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(assertStmtMetaModel, "getCheck", "setCheck", "check", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "check"), true, false, false, false, false));
        assertStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(assertStmtMetaModel, "getMessage", "setMessage", "message", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "message"), true, true, false, false, false));
        blockStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(blockStmtMetaModel, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, getField(BlockStmt.class, "statements"), true, false, true, false, false));
        breakStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(breakStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(BreakStmt.class, "label"), true, true, false, false, false));
        catchClauseMetaModel.propertyMetaModels.add(new PropertyMetaModel(catchClauseMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(CatchClause.class, "body"), true, false, false, false, false));
        catchClauseMetaModel.propertyMetaModels.add(new PropertyMetaModel(catchClauseMetaModel, "getParameter", "setParameter", "parameter", com.github.javaparser.ast.body.Parameter.class, getField(CatchClause.class, "parameter"), true, false, false, false, false));
        continueStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(continueStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(ContinueStmt.class, "label"), true, true, false, false, false));
        doStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(doStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(DoStmt.class, "body"), true, false, false, false, false));
        doStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(doStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(DoStmt.class, "condition"), true, false, false, false, false));
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "arguments"), true, false, true, false, false));
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "expression"), true, true, false, false, false));
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "isThis", "setIsThis", "isThis", boolean.class, getField(ExplicitConstructorInvocationStmt.class, "isThis"), true, false, false, false, false));
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ExplicitConstructorInvocationStmt.class, "typeArguments"), true, true, true, false, false));
        expressionStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(expressionStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExpressionStmt.class, "expression"), true, false, false, false, false));
        foreachStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(foreachStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForeachStmt.class, "body"), true, false, false, false, false));
        foreachStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(foreachStmtMetaModel, "getIterable", "setIterable", "iterable", com.github.javaparser.ast.expr.Expression.class, getField(ForeachStmt.class, "iterable"), true, false, false, false, false));
        foreachStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(foreachStmtMetaModel, "getVariable", "setVariable", "variable", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(ForeachStmt.class, "variable"), true, false, false, false, false));
        forStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(forStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForStmt.class, "body"), true, false, false, false, false));
        forStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(forStmtMetaModel, "getCompare", "setCompare", "compare", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "compare"), true, true, false, false, false));
        forStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(forStmtMetaModel, "getInitialization", "setInitialization", "initialization", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "initialization"), true, false, true, false, false));
        forStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(forStmtMetaModel, "getUpdate", "setUpdate", "update", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "update"), true, false, true, false, false));
        ifStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(ifStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(IfStmt.class, "condition"), true, false, false, false, false));
        ifStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(ifStmtMetaModel, "getElseStmt", "setElseStmt", "elseStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "elseStmt"), true, true, false, false, false));
        ifStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(ifStmtMetaModel, "getThenStmt", "setThenStmt", "thenStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "thenStmt"), true, false, false, false, false));
        labeledStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(labeledStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(LabeledStmt.class, "label"), true, false, false, false, false));
        labeledStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(labeledStmtMetaModel, "getStatement", "setStatement", "statement", com.github.javaparser.ast.stmt.Statement.class, getField(LabeledStmt.class, "statement"), true, false, false, false, false));
        returnStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(returnStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ReturnStmt.class, "expression"), true, true, false, false, false));
        switchEntryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(switchEntryStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.Expression.class, getField(SwitchEntryStmt.class, "label"), true, true, false, false, false));
        switchEntryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(switchEntryStmtMetaModel, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, getField(SwitchEntryStmt.class, "statements"), true, false, true, false, false));
        switchStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(switchStmtMetaModel, "getEntries", "setEntries", "entries", com.github.javaparser.ast.stmt.SwitchEntryStmt.class, getField(SwitchStmt.class, "entries"), true, false, true, false, false));
        switchStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(switchStmtMetaModel, "getSelector", "setSelector", "selector", com.github.javaparser.ast.expr.Expression.class, getField(SwitchStmt.class, "selector"), true, false, false, false, false));
        synchronizedStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(synchronizedStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(SynchronizedStmt.class, "body"), true, false, false, false, false));
        synchronizedStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(synchronizedStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(SynchronizedStmt.class, "expression"), true, false, false, false, false));
        throwStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(throwStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ThrowStmt.class, "expression"), true, false, false, false, false));
        tryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(tryStmtMetaModel, "getCatchClauses", "setCatchClauses", "catchClauses", com.github.javaparser.ast.stmt.CatchClause.class, getField(TryStmt.class, "catchClauses"), true, false, true, false, false));
        tryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(tryStmtMetaModel, "getFinallyBlock", "setFinallyBlock", "finallyBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "finallyBlock"), true, true, false, false, false));
        tryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(tryStmtMetaModel, "getResources", "setResources", "resources", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(TryStmt.class, "resources"), true, false, true, false, false));
        tryStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(tryStmtMetaModel, "getTryBlock", "setTryBlock", "tryBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "tryBlock"), true, true, false, false, false));
        localClassDeclarationStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(localClassDeclarationStmtMetaModel, "getClassDeclaration", "setClassDeclaration", "classDeclaration", com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, getField(LocalClassDeclarationStmt.class, "classDeclaration"), true, false, false, false, false));
        whileStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(whileStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(WhileStmt.class, "body"), true, false, false, false, false));
        whileStmtMetaModel.propertyMetaModels.add(new PropertyMetaModel(whileStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(WhileStmt.class, "condition"), true, false, false, false, false));
        arrayTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(arrayTypeMetaModel, "getComponentType", "setComponentType", "componentType", com.github.javaparser.ast.type.Type.class, getField(ArrayType.class, "componentType"), true, false, false, false, false));
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceTypeMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ClassOrInterfaceType.class, "name"), true, false, false, false, false));
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceTypeMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceType.class, "scope"), true, true, false, false, false));
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(classOrInterfaceTypeMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ClassOrInterfaceType.class, "typeArguments"), true, true, true, false, false));
        intersectionTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(intersectionTypeMetaModel, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(IntersectionType.class, "elements"), true, false, true, false, false));
        primitiveTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(primitiveTypeMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.PrimitiveType.Primitive.class, getField(PrimitiveType.class, "type"), true, false, false, false, false));
        typeParameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeParameterMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeParameter.class, "name"), true, false, false, false, false));
        typeParameterMetaModel.propertyMetaModels.add(new PropertyMetaModel(typeParameterMetaModel, "getTypeBound", "setTypeBound", "typeBound", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(TypeParameter.class, "typeBound"), true, false, true, false, false));
        unionTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(unionTypeMetaModel, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(UnionType.class, "elements"), true, false, true, false, false));
        wildcardTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(wildcardTypeMetaModel, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "extendedTypes"), true, true, false, false, false));
        wildcardTypeMetaModel.propertyMetaModels.add(new PropertyMetaModel(wildcardTypeMetaModel, "getSuperTypes", "setSuperTypes", "superTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "superTypes"), true, true, false, false, false));
    }

    public Optional<BaseNodeMetaModel> getClassMetaModel(Class<?> c) {
        for (BaseNodeMetaModel oldClassMetaModel : classMetaModels) {
            if (oldClassMetaModel.name.equals(c.getSimpleName())) {
                return Optional.of(oldClassMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (BaseNodeMetaModel classMetaModel : classMetaModels) {
            b.append(classMetaModel).append("\n");
            for (PropertyMetaModel propertyMetaModel : classMetaModel.propertyMetaModels) {
                b.append("\t").append(propertyMetaModel).append("\n");
            }
        }
        return b.toString();
    }

    private Field getField(Class<?> c, String name) {
        try {
            return c.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }

    public final BaseNodeMetaModel nodeListMetaModel = new NodeListMetaModel(this, Optional.empty());

    public final BaseNodeMetaModel nodeMetaModel = new NodeMetaModel(this, Optional.empty());

    public final BaseNodeMetaModel bodyDeclarationMetaModel = new BodyDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel statementMetaModel = new StatementMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel expressionMetaModel = new ExpressionMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel typeMetaModel = new TypeMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel annotationExprMetaModel = new AnnotationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel typeDeclarationMetaModel = new TypeDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel literalExprMetaModel = new LiteralExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel referenceTypeMetaModel = new ReferenceTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel stringLiteralExprMetaModel = new StringLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final BaseNodeMetaModel arrayCreationLevelMetaModel = new ArrayCreationLevelMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel compilationUnitMetaModel = new CompilationUnitMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel packageDeclarationMetaModel = new PackageDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel annotationDeclarationMetaModel = new AnnotationDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final BaseNodeMetaModel annotationMemberDeclarationMetaModel = new AnnotationMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel classOrInterfaceDeclarationMetaModel = new ClassOrInterfaceDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final BaseNodeMetaModel constructorDeclarationMetaModel = new ConstructorDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel emptyMemberDeclarationMetaModel = new EmptyMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel enumConstantDeclarationMetaModel = new EnumConstantDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel enumDeclarationMetaModel = new EnumDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final BaseNodeMetaModel fieldDeclarationMetaModel = new FieldDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel initializerDeclarationMetaModel = new InitializerDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel methodDeclarationMetaModel = new MethodDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final BaseNodeMetaModel parameterMetaModel = new ParameterMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel variableDeclaratorMetaModel = new VariableDeclaratorMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel commentMetaModel = new CommentMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel blockCommentMetaModel = new BlockCommentMetaModel(this, Optional.of(commentMetaModel));

    public final BaseNodeMetaModel javadocCommentMetaModel = new JavadocCommentMetaModel(this, Optional.of(commentMetaModel));

    public final BaseNodeMetaModel lineCommentMetaModel = new LineCommentMetaModel(this, Optional.of(commentMetaModel));

    public final BaseNodeMetaModel arrayAccessExprMetaModel = new ArrayAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel arrayCreationExprMetaModel = new ArrayCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel arrayInitializerExprMetaModel = new ArrayInitializerExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel assignExprMetaModel = new AssignExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel binaryExprMetaModel = new BinaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel booleanLiteralExprMetaModel = new BooleanLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final BaseNodeMetaModel castExprMetaModel = new CastExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel charLiteralExprMetaModel = new CharLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final BaseNodeMetaModel classExprMetaModel = new ClassExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel conditionalExprMetaModel = new ConditionalExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel doubleLiteralExprMetaModel = new DoubleLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final BaseNodeMetaModel enclosedExprMetaModel = new EnclosedExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel fieldAccessExprMetaModel = new FieldAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel instanceOfExprMetaModel = new InstanceOfExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel integerLiteralExprMetaModel = new IntegerLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final BaseNodeMetaModel lambdaExprMetaModel = new LambdaExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel longLiteralExprMetaModel = new LongLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final BaseNodeMetaModel markerAnnotationExprMetaModel = new MarkerAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final BaseNodeMetaModel memberValuePairMetaModel = new MemberValuePairMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel methodCallExprMetaModel = new MethodCallExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel methodReferenceExprMetaModel = new MethodReferenceExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel nameExprMetaModel = new NameExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel nameMetaModel = new NameMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel normalAnnotationExprMetaModel = new NormalAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final BaseNodeMetaModel nullLiteralExprMetaModel = new NullLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final BaseNodeMetaModel objectCreationExprMetaModel = new ObjectCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel simpleNameMetaModel = new SimpleNameMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel singleMemberAnnotationExprMetaModel = new SingleMemberAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final BaseNodeMetaModel superExprMetaModel = new SuperExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel thisExprMetaModel = new ThisExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel typeExprMetaModel = new TypeExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel unaryExprMetaModel = new UnaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel variableDeclarationExprMetaModel = new VariableDeclarationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BaseNodeMetaModel importDeclarationMetaModel = new ImportDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel assertStmtMetaModel = new AssertStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel blockStmtMetaModel = new BlockStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel breakStmtMetaModel = new BreakStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel catchClauseMetaModel = new CatchClauseMetaModel(this, Optional.of(nodeMetaModel));

    public final BaseNodeMetaModel continueStmtMetaModel = new ContinueStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel doStmtMetaModel = new DoStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel emptyStmtMetaModel = new EmptyStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel explicitConstructorInvocationStmtMetaModel = new ExplicitConstructorInvocationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel expressionStmtMetaModel = new ExpressionStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel foreachStmtMetaModel = new ForeachStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel forStmtMetaModel = new ForStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel ifStmtMetaModel = new IfStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel labeledStmtMetaModel = new LabeledStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel returnStmtMetaModel = new ReturnStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel switchEntryStmtMetaModel = new SwitchEntryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel switchStmtMetaModel = new SwitchStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel synchronizedStmtMetaModel = new SynchronizedStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel throwStmtMetaModel = new ThrowStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel tryStmtMetaModel = new TryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel localClassDeclarationStmtMetaModel = new LocalClassDeclarationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel whileStmtMetaModel = new WhileStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BaseNodeMetaModel arrayTypeMetaModel = new ArrayTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final BaseNodeMetaModel classOrInterfaceTypeMetaModel = new ClassOrInterfaceTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final BaseNodeMetaModel intersectionTypeMetaModel = new IntersectionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel primitiveTypeMetaModel = new PrimitiveTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel typeParameterMetaModel = new TypeParameterMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final BaseNodeMetaModel unionTypeMetaModel = new UnionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel unknownTypeMetaModel = new UnknownTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel voidTypeMetaModel = new VoidTypeMetaModel(this, Optional.of(typeMetaModel));

    public final BaseNodeMetaModel wildcardTypeMetaModel = new WildcardTypeMetaModel(this, Optional.of(typeMetaModel));
}

