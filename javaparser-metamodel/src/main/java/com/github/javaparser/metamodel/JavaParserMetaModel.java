package com.github.javaparser.metamodel;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import javax.annotation.Generated;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The model contains meta-data about all nodes in the AST.
 */
public class JavaParserMetaModel {

    public final List<BaseNodeMetaModel> nodeMetaModels = new ArrayList<>();

    public JavaParserMetaModel() {
        initializeNodeMetaModels();
        initializeFieldMetaModels();
    }

    private void initializeNodeMetaModels() {
        nodeMetaModels.add(annotationDeclarationMetaModel);
        nodeMetaModels.add(annotationExprMetaModel);
        nodeMetaModels.add(annotationMemberDeclarationMetaModel);
        nodeMetaModels.add(arrayAccessExprMetaModel);
        nodeMetaModels.add(arrayCreationExprMetaModel);
        nodeMetaModels.add(arrayCreationLevelMetaModel);
        nodeMetaModels.add(arrayInitializerExprMetaModel);
        nodeMetaModels.add(arrayTypeMetaModel);
        nodeMetaModels.add(assertStmtMetaModel);
        nodeMetaModels.add(assignExprMetaModel);
        nodeMetaModels.add(binaryExprMetaModel);
        nodeMetaModels.add(blockCommentMetaModel);
        nodeMetaModels.add(blockStmtMetaModel);
        nodeMetaModels.add(bodyDeclarationMetaModel);
        nodeMetaModels.add(booleanLiteralExprMetaModel);
        nodeMetaModels.add(breakStmtMetaModel);
        nodeMetaModels.add(castExprMetaModel);
        nodeMetaModels.add(catchClauseMetaModel);
        nodeMetaModels.add(charLiteralExprMetaModel);
        nodeMetaModels.add(classExprMetaModel);
        nodeMetaModels.add(classOrInterfaceDeclarationMetaModel);
        nodeMetaModels.add(classOrInterfaceTypeMetaModel);
        nodeMetaModels.add(commentMetaModel);
        nodeMetaModels.add(compilationUnitMetaModel);
        nodeMetaModels.add(conditionalExprMetaModel);
        nodeMetaModels.add(constructorDeclarationMetaModel);
        nodeMetaModels.add(continueStmtMetaModel);
        nodeMetaModels.add(doStmtMetaModel);
        nodeMetaModels.add(doubleLiteralExprMetaModel);
        nodeMetaModels.add(emptyMemberDeclarationMetaModel);
        nodeMetaModels.add(emptyStmtMetaModel);
        nodeMetaModels.add(enclosedExprMetaModel);
        nodeMetaModels.add(enumConstantDeclarationMetaModel);
        nodeMetaModels.add(enumDeclarationMetaModel);
        nodeMetaModels.add(explicitConstructorInvocationStmtMetaModel);
        nodeMetaModels.add(expressionMetaModel);
        nodeMetaModels.add(expressionStmtMetaModel);
        nodeMetaModels.add(fieldAccessExprMetaModel);
        nodeMetaModels.add(fieldDeclarationMetaModel);
        nodeMetaModels.add(forStmtMetaModel);
        nodeMetaModels.add(foreachStmtMetaModel);
        nodeMetaModels.add(ifStmtMetaModel);
        nodeMetaModels.add(importDeclarationMetaModel);
        nodeMetaModels.add(initializerDeclarationMetaModel);
        nodeMetaModels.add(instanceOfExprMetaModel);
        nodeMetaModels.add(integerLiteralExprMetaModel);
        nodeMetaModels.add(intersectionTypeMetaModel);
        nodeMetaModels.add(javadocCommentMetaModel);
        nodeMetaModels.add(labeledStmtMetaModel);
        nodeMetaModels.add(lambdaExprMetaModel);
        nodeMetaModels.add(lineCommentMetaModel);
        nodeMetaModels.add(literalExprMetaModel);
        nodeMetaModels.add(localClassDeclarationStmtMetaModel);
        nodeMetaModels.add(longLiteralExprMetaModel);
        nodeMetaModels.add(markerAnnotationExprMetaModel);
        nodeMetaModels.add(memberValuePairMetaModel);
        nodeMetaModels.add(methodCallExprMetaModel);
        nodeMetaModels.add(methodDeclarationMetaModel);
        nodeMetaModels.add(methodReferenceExprMetaModel);
        nodeMetaModels.add(nameExprMetaModel);
        nodeMetaModels.add(nameMetaModel);
        nodeMetaModels.add(nodeMetaModel);
        nodeMetaModels.add(normalAnnotationExprMetaModel);
        nodeMetaModels.add(nullLiteralExprMetaModel);
        nodeMetaModels.add(objectCreationExprMetaModel);
        nodeMetaModels.add(packageDeclarationMetaModel);
        nodeMetaModels.add(parameterMetaModel);
        nodeMetaModels.add(primitiveTypeMetaModel);
        nodeMetaModels.add(referenceTypeMetaModel);
        nodeMetaModels.add(returnStmtMetaModel);
        nodeMetaModels.add(simpleNameMetaModel);
        nodeMetaModels.add(singleMemberAnnotationExprMetaModel);
        nodeMetaModels.add(statementMetaModel);
        nodeMetaModels.add(stringLiteralExprMetaModel);
        nodeMetaModels.add(superExprMetaModel);
        nodeMetaModels.add(switchEntryStmtMetaModel);
        nodeMetaModels.add(switchStmtMetaModel);
        nodeMetaModels.add(synchronizedStmtMetaModel);
        nodeMetaModels.add(thisExprMetaModel);
        nodeMetaModels.add(throwStmtMetaModel);
        nodeMetaModels.add(tryStmtMetaModel);
        nodeMetaModels.add(typeDeclarationMetaModel);
        nodeMetaModels.add(typeExprMetaModel);
        nodeMetaModels.add(typeMetaModel);
        nodeMetaModels.add(typeParameterMetaModel);
        nodeMetaModels.add(unaryExprMetaModel);
        nodeMetaModels.add(unionTypeMetaModel);
        nodeMetaModels.add(unknownTypeMetaModel);
        nodeMetaModels.add(variableDeclarationExprMetaModel);
        nodeMetaModels.add(variableDeclaratorMetaModel);
        nodeMetaModels.add(voidTypeMetaModel);
        nodeMetaModels.add(whileStmtMetaModel);
        nodeMetaModels.add(wildcardTypeMetaModel);
    }

    private void initializeFieldMetaModels() {
        nodeMetaModel.commentPropertyMetaModel = new PropertyMetaModel(nodeMetaModel, "comment", com.github.javaparser.ast.comments.Comment.class, getField(Node.class, "comment"), true, false, false, false, false);
        nodeMetaModel.propertyMetaModels.add(nodeMetaModel.commentPropertyMetaModel);
        bodyDeclarationMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(bodyDeclarationMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(BodyDeclaration.class, "annotations"), true, false, true, false, false);
        bodyDeclarationMetaModel.propertyMetaModels.add(bodyDeclarationMetaModel.annotationsPropertyMetaModel);
        typeMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(typeMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Type.class, "annotations"), true, false, true, false, false);
        typeMetaModel.propertyMetaModels.add(typeMetaModel.annotationsPropertyMetaModel);
        annotationExprMetaModel.namePropertyMetaModel = new PropertyMetaModel(annotationExprMetaModel, "name", com.github.javaparser.ast.expr.Name.class, getField(AnnotationExpr.class, "name"), true, false, false, false, false);
        annotationExprMetaModel.propertyMetaModels.add(annotationExprMetaModel.namePropertyMetaModel);
        typeDeclarationMetaModel.membersPropertyMetaModel = new PropertyMetaModel(typeDeclarationMetaModel, "members", com.github.javaparser.ast.body.BodyDeclaration.class, getField(TypeDeclaration.class, "members"), true, false, true, false, true);
        typeDeclarationMetaModel.propertyMetaModels.add(typeDeclarationMetaModel.membersPropertyMetaModel);
        typeDeclarationMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(typeDeclarationMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(TypeDeclaration.class, "modifiers"), true, false, false, true, false);
        typeDeclarationMetaModel.propertyMetaModels.add(typeDeclarationMetaModel.modifiersPropertyMetaModel);
        typeDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(typeDeclarationMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeDeclaration.class, "name"), true, false, false, false, false);
        typeDeclarationMetaModel.propertyMetaModels.add(typeDeclarationMetaModel.namePropertyMetaModel);
        stringLiteralExprMetaModel.valuePropertyMetaModel = new PropertyMetaModel(stringLiteralExprMetaModel, "value", java.lang.String.class, getField(StringLiteralExpr.class, "value"), true, false, false, false, false);
        stringLiteralExprMetaModel.propertyMetaModels.add(stringLiteralExprMetaModel.valuePropertyMetaModel);
        arrayCreationLevelMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(arrayCreationLevelMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(ArrayCreationLevel.class, "annotations"), true, false, true, false, false);
        arrayCreationLevelMetaModel.propertyMetaModels.add(arrayCreationLevelMetaModel.annotationsPropertyMetaModel);
        arrayCreationLevelMetaModel.dimensionPropertyMetaModel = new PropertyMetaModel(arrayCreationLevelMetaModel, "dimension", com.github.javaparser.ast.expr.Expression.class, getField(ArrayCreationLevel.class, "dimension"), true, true, false, false, false);
        arrayCreationLevelMetaModel.propertyMetaModels.add(arrayCreationLevelMetaModel.dimensionPropertyMetaModel);
        compilationUnitMetaModel.importsPropertyMetaModel = new PropertyMetaModel(compilationUnitMetaModel, "imports", com.github.javaparser.ast.ImportDeclaration.class, getField(CompilationUnit.class, "imports"), true, false, true, false, false);
        compilationUnitMetaModel.propertyMetaModels.add(compilationUnitMetaModel.importsPropertyMetaModel);
        compilationUnitMetaModel.packageDeclarationPropertyMetaModel = new PropertyMetaModel(compilationUnitMetaModel, "packageDeclaration", com.github.javaparser.ast.PackageDeclaration.class, getField(CompilationUnit.class, "packageDeclaration"), true, true, false, false, false);
        compilationUnitMetaModel.propertyMetaModels.add(compilationUnitMetaModel.packageDeclarationPropertyMetaModel);
        compilationUnitMetaModel.typesPropertyMetaModel = new PropertyMetaModel(compilationUnitMetaModel, "types", com.github.javaparser.ast.body.TypeDeclaration.class, getField(CompilationUnit.class, "types"), true, false, true, false, true);
        compilationUnitMetaModel.propertyMetaModels.add(compilationUnitMetaModel.typesPropertyMetaModel);
        packageDeclarationMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(packageDeclarationMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(PackageDeclaration.class, "annotations"), true, false, true, false, false);
        packageDeclarationMetaModel.propertyMetaModels.add(packageDeclarationMetaModel.annotationsPropertyMetaModel);
        packageDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(packageDeclarationMetaModel, "name", com.github.javaparser.ast.expr.Name.class, getField(PackageDeclaration.class, "name"), true, false, false, false, false);
        packageDeclarationMetaModel.propertyMetaModels.add(packageDeclarationMetaModel.namePropertyMetaModel);
        annotationMemberDeclarationMetaModel.defaultValuePropertyMetaModel = new PropertyMetaModel(annotationMemberDeclarationMetaModel, "defaultValue", com.github.javaparser.ast.expr.Expression.class, getField(AnnotationMemberDeclaration.class, "defaultValue"), true, true, false, false, false);
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(annotationMemberDeclarationMetaModel.defaultValuePropertyMetaModel);
        annotationMemberDeclarationMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(annotationMemberDeclarationMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(AnnotationMemberDeclaration.class, "modifiers"), true, false, false, true, false);
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(annotationMemberDeclarationMetaModel.modifiersPropertyMetaModel);
        annotationMemberDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(annotationMemberDeclarationMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(AnnotationMemberDeclaration.class, "name"), true, false, false, false, false);
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(annotationMemberDeclarationMetaModel.namePropertyMetaModel);
        annotationMemberDeclarationMetaModel.typePropertyMetaModel = new PropertyMetaModel(annotationMemberDeclarationMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(AnnotationMemberDeclaration.class, "type"), true, false, false, false, false);
        annotationMemberDeclarationMetaModel.propertyMetaModels.add(annotationMemberDeclarationMetaModel.typePropertyMetaModel);
        classOrInterfaceDeclarationMetaModel.extendedTypesPropertyMetaModel = new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "extendedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "extendedTypes"), true, false, true, false, false);
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(classOrInterfaceDeclarationMetaModel.extendedTypesPropertyMetaModel);
        classOrInterfaceDeclarationMetaModel.implementedTypesPropertyMetaModel = new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "implementedTypes"), true, false, true, false, false);
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(classOrInterfaceDeclarationMetaModel.implementedTypesPropertyMetaModel);
        classOrInterfaceDeclarationMetaModel.isInterfacePropertyMetaModel = new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "isInterface", boolean.class, getField(ClassOrInterfaceDeclaration.class, "isInterface"), true, false, false, false, false);
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(classOrInterfaceDeclarationMetaModel.isInterfacePropertyMetaModel);
        classOrInterfaceDeclarationMetaModel.typeParametersPropertyMetaModel = new PropertyMetaModel(classOrInterfaceDeclarationMetaModel, "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ClassOrInterfaceDeclaration.class, "typeParameters"), true, false, true, false, false);
        classOrInterfaceDeclarationMetaModel.propertyMetaModels.add(classOrInterfaceDeclarationMetaModel.typeParametersPropertyMetaModel);
        constructorDeclarationMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(ConstructorDeclaration.class, "body"), true, false, false, false, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.bodyPropertyMetaModel);
        constructorDeclarationMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(ConstructorDeclaration.class, "modifiers"), true, false, false, true, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.modifiersPropertyMetaModel);
        constructorDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ConstructorDeclaration.class, "name"), true, false, false, false, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.namePropertyMetaModel);
        constructorDeclarationMetaModel.parametersPropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "parameters", com.github.javaparser.ast.body.Parameter.class, getField(ConstructorDeclaration.class, "parameters"), true, false, true, false, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.parametersPropertyMetaModel);
        constructorDeclarationMetaModel.thrownExceptionsPropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(ConstructorDeclaration.class, "thrownExceptions"), true, false, true, false, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.thrownExceptionsPropertyMetaModel);
        constructorDeclarationMetaModel.typeParametersPropertyMetaModel = new PropertyMetaModel(constructorDeclarationMetaModel, "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ConstructorDeclaration.class, "typeParameters"), true, false, true, false, false);
        constructorDeclarationMetaModel.propertyMetaModels.add(constructorDeclarationMetaModel.typeParametersPropertyMetaModel);
        enumConstantDeclarationMetaModel.argumentsPropertyMetaModel = new PropertyMetaModel(enumConstantDeclarationMetaModel, "arguments", com.github.javaparser.ast.expr.Expression.class, getField(EnumConstantDeclaration.class, "arguments"), true, false, true, false, false);
        enumConstantDeclarationMetaModel.propertyMetaModels.add(enumConstantDeclarationMetaModel.argumentsPropertyMetaModel);
        enumConstantDeclarationMetaModel.classBodyPropertyMetaModel = new PropertyMetaModel(enumConstantDeclarationMetaModel, "classBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(EnumConstantDeclaration.class, "classBody"), true, false, true, false, true);
        enumConstantDeclarationMetaModel.propertyMetaModels.add(enumConstantDeclarationMetaModel.classBodyPropertyMetaModel);
        enumConstantDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(enumConstantDeclarationMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(EnumConstantDeclaration.class, "name"), true, false, false, false, false);
        enumConstantDeclarationMetaModel.propertyMetaModels.add(enumConstantDeclarationMetaModel.namePropertyMetaModel);
        enumDeclarationMetaModel.entriesPropertyMetaModel = new PropertyMetaModel(enumDeclarationMetaModel, "entries", com.github.javaparser.ast.body.EnumConstantDeclaration.class, getField(EnumDeclaration.class, "entries"), true, false, true, false, false);
        enumDeclarationMetaModel.propertyMetaModels.add(enumDeclarationMetaModel.entriesPropertyMetaModel);
        enumDeclarationMetaModel.implementedTypesPropertyMetaModel = new PropertyMetaModel(enumDeclarationMetaModel, "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(EnumDeclaration.class, "implementedTypes"), true, false, true, false, false);
        enumDeclarationMetaModel.propertyMetaModels.add(enumDeclarationMetaModel.implementedTypesPropertyMetaModel);
        fieldDeclarationMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(fieldDeclarationMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(FieldDeclaration.class, "modifiers"), true, false, false, true, false);
        fieldDeclarationMetaModel.propertyMetaModels.add(fieldDeclarationMetaModel.modifiersPropertyMetaModel);
        fieldDeclarationMetaModel.variablesPropertyMetaModel = new PropertyMetaModel(fieldDeclarationMetaModel, "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(FieldDeclaration.class, "variables"), true, false, true, false, false);
        fieldDeclarationMetaModel.propertyMetaModels.add(fieldDeclarationMetaModel.variablesPropertyMetaModel);
        initializerDeclarationMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(initializerDeclarationMetaModel, "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(InitializerDeclaration.class, "body"), true, false, false, false, false);
        initializerDeclarationMetaModel.propertyMetaModels.add(initializerDeclarationMetaModel.bodyPropertyMetaModel);
        initializerDeclarationMetaModel.isStaticPropertyMetaModel = new PropertyMetaModel(initializerDeclarationMetaModel, "isStatic", boolean.class, getField(InitializerDeclaration.class, "isStatic"), true, false, false, false, false);
        initializerDeclarationMetaModel.propertyMetaModels.add(initializerDeclarationMetaModel.isStaticPropertyMetaModel);
        methodDeclarationMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(MethodDeclaration.class, "body"), true, true, false, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.bodyPropertyMetaModel);
        methodDeclarationMetaModel.isDefaultPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "isDefault", boolean.class, getField(MethodDeclaration.class, "isDefault"), true, false, false, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.isDefaultPropertyMetaModel);
        methodDeclarationMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(MethodDeclaration.class, "modifiers"), true, false, false, true, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.modifiersPropertyMetaModel);
        methodDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodDeclaration.class, "name"), true, false, false, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.namePropertyMetaModel);
        methodDeclarationMetaModel.parametersPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "parameters", com.github.javaparser.ast.body.Parameter.class, getField(MethodDeclaration.class, "parameters"), true, false, true, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.parametersPropertyMetaModel);
        methodDeclarationMetaModel.thrownExceptionsPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(MethodDeclaration.class, "thrownExceptions"), true, false, true, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.thrownExceptionsPropertyMetaModel);
        methodDeclarationMetaModel.typePropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(MethodDeclaration.class, "type"), true, false, false, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.typePropertyMetaModel);
        methodDeclarationMetaModel.typeParametersPropertyMetaModel = new PropertyMetaModel(methodDeclarationMetaModel, "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(MethodDeclaration.class, "typeParameters"), true, false, true, false, false);
        methodDeclarationMetaModel.propertyMetaModels.add(methodDeclarationMetaModel.typeParametersPropertyMetaModel);
        parameterMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(parameterMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Parameter.class, "annotations"), true, false, true, false, false);
        parameterMetaModel.propertyMetaModels.add(parameterMetaModel.annotationsPropertyMetaModel);
        parameterMetaModel.isVarArgsPropertyMetaModel = new PropertyMetaModel(parameterMetaModel, "isVarArgs", boolean.class, getField(Parameter.class, "isVarArgs"), true, false, false, false, false);
        parameterMetaModel.propertyMetaModels.add(parameterMetaModel.isVarArgsPropertyMetaModel);
        parameterMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(parameterMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(Parameter.class, "modifiers"), true, false, false, true, false);
        parameterMetaModel.propertyMetaModels.add(parameterMetaModel.modifiersPropertyMetaModel);
        parameterMetaModel.namePropertyMetaModel = new PropertyMetaModel(parameterMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(Parameter.class, "name"), true, false, false, false, false);
        parameterMetaModel.propertyMetaModels.add(parameterMetaModel.namePropertyMetaModel);
        parameterMetaModel.typePropertyMetaModel = new PropertyMetaModel(parameterMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(Parameter.class, "type"), true, false, false, false, false);
        parameterMetaModel.propertyMetaModels.add(parameterMetaModel.typePropertyMetaModel);
        variableDeclaratorMetaModel.initializerPropertyMetaModel = new PropertyMetaModel(variableDeclaratorMetaModel, "initializer", com.github.javaparser.ast.expr.Expression.class, getField(VariableDeclarator.class, "initializer"), true, true, false, false, false);
        variableDeclaratorMetaModel.propertyMetaModels.add(variableDeclaratorMetaModel.initializerPropertyMetaModel);
        variableDeclaratorMetaModel.namePropertyMetaModel = new PropertyMetaModel(variableDeclaratorMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(VariableDeclarator.class, "name"), true, false, false, false, false);
        variableDeclaratorMetaModel.propertyMetaModels.add(variableDeclaratorMetaModel.namePropertyMetaModel);
        variableDeclaratorMetaModel.typePropertyMetaModel = new PropertyMetaModel(variableDeclaratorMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(VariableDeclarator.class, "type"), true, false, false, false, false);
        variableDeclaratorMetaModel.propertyMetaModels.add(variableDeclaratorMetaModel.typePropertyMetaModel);
        commentMetaModel.commentedNodePropertyMetaModel = new PropertyMetaModel(commentMetaModel, "commentedNode", com.github.javaparser.ast.Node.class, getField(Comment.class, "commentedNode"), true, true, false, false, false);
        commentMetaModel.propertyMetaModels.add(commentMetaModel.commentedNodePropertyMetaModel);
        commentMetaModel.contentPropertyMetaModel = new PropertyMetaModel(commentMetaModel, "content", java.lang.String.class, getField(Comment.class, "content"), true, false, false, false, false);
        commentMetaModel.propertyMetaModels.add(commentMetaModel.contentPropertyMetaModel);
        arrayAccessExprMetaModel.indexPropertyMetaModel = new PropertyMetaModel(arrayAccessExprMetaModel, "index", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "index"), true, false, false, false, false);
        arrayAccessExprMetaModel.propertyMetaModels.add(arrayAccessExprMetaModel.indexPropertyMetaModel);
        arrayAccessExprMetaModel.namePropertyMetaModel = new PropertyMetaModel(arrayAccessExprMetaModel, "name", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "name"), true, false, false, false, false);
        arrayAccessExprMetaModel.propertyMetaModels.add(arrayAccessExprMetaModel.namePropertyMetaModel);
        arrayCreationExprMetaModel.elementTypePropertyMetaModel = new PropertyMetaModel(arrayCreationExprMetaModel, "elementType", com.github.javaparser.ast.type.Type.class, getField(ArrayCreationExpr.class, "elementType"), true, false, false, false, false);
        arrayCreationExprMetaModel.propertyMetaModels.add(arrayCreationExprMetaModel.elementTypePropertyMetaModel);
        arrayCreationExprMetaModel.initializerPropertyMetaModel = new PropertyMetaModel(arrayCreationExprMetaModel, "initializer", com.github.javaparser.ast.expr.ArrayInitializerExpr.class, getField(ArrayCreationExpr.class, "initializer"), true, true, false, false, false);
        arrayCreationExprMetaModel.propertyMetaModels.add(arrayCreationExprMetaModel.initializerPropertyMetaModel);
        arrayCreationExprMetaModel.levelsPropertyMetaModel = new PropertyMetaModel(arrayCreationExprMetaModel, "levels", com.github.javaparser.ast.ArrayCreationLevel.class, getField(ArrayCreationExpr.class, "levels"), true, false, true, false, false);
        arrayCreationExprMetaModel.propertyMetaModels.add(arrayCreationExprMetaModel.levelsPropertyMetaModel);
        arrayInitializerExprMetaModel.valuesPropertyMetaModel = new PropertyMetaModel(arrayInitializerExprMetaModel, "values", com.github.javaparser.ast.expr.Expression.class, getField(ArrayInitializerExpr.class, "values"), true, false, true, false, false);
        arrayInitializerExprMetaModel.propertyMetaModels.add(arrayInitializerExprMetaModel.valuesPropertyMetaModel);
        assignExprMetaModel.operatorPropertyMetaModel = new PropertyMetaModel(assignExprMetaModel, "operator", com.github.javaparser.ast.expr.AssignExpr.Operator.class, getField(AssignExpr.class, "operator"), true, false, false, false, false);
        assignExprMetaModel.propertyMetaModels.add(assignExprMetaModel.operatorPropertyMetaModel);
        assignExprMetaModel.targetPropertyMetaModel = new PropertyMetaModel(assignExprMetaModel, "target", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "target"), true, false, false, false, false);
        assignExprMetaModel.propertyMetaModels.add(assignExprMetaModel.targetPropertyMetaModel);
        assignExprMetaModel.valuePropertyMetaModel = new PropertyMetaModel(assignExprMetaModel, "value", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "value"), true, false, false, false, false);
        assignExprMetaModel.propertyMetaModels.add(assignExprMetaModel.valuePropertyMetaModel);
        binaryExprMetaModel.leftPropertyMetaModel = new PropertyMetaModel(binaryExprMetaModel, "left", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "left"), true, false, false, false, false);
        binaryExprMetaModel.propertyMetaModels.add(binaryExprMetaModel.leftPropertyMetaModel);
        binaryExprMetaModel.operatorPropertyMetaModel = new PropertyMetaModel(binaryExprMetaModel, "operator", com.github.javaparser.ast.expr.BinaryExpr.Operator.class, getField(BinaryExpr.class, "operator"), true, false, false, false, false);
        binaryExprMetaModel.propertyMetaModels.add(binaryExprMetaModel.operatorPropertyMetaModel);
        binaryExprMetaModel.rightPropertyMetaModel = new PropertyMetaModel(binaryExprMetaModel, "right", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "right"), true, false, false, false, false);
        binaryExprMetaModel.propertyMetaModels.add(binaryExprMetaModel.rightPropertyMetaModel);
        booleanLiteralExprMetaModel.valuePropertyMetaModel = new PropertyMetaModel(booleanLiteralExprMetaModel, "value", boolean.class, getField(BooleanLiteralExpr.class, "value"), true, false, false, false, false);
        booleanLiteralExprMetaModel.propertyMetaModels.add(booleanLiteralExprMetaModel.valuePropertyMetaModel);
        castExprMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(castExprMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(CastExpr.class, "expression"), true, false, false, false, false);
        castExprMetaModel.propertyMetaModels.add(castExprMetaModel.expressionPropertyMetaModel);
        castExprMetaModel.typePropertyMetaModel = new PropertyMetaModel(castExprMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(CastExpr.class, "type"), true, false, false, false, false);
        castExprMetaModel.propertyMetaModels.add(castExprMetaModel.typePropertyMetaModel);
        classExprMetaModel.typePropertyMetaModel = new PropertyMetaModel(classExprMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(ClassExpr.class, "type"), true, false, false, false, false);
        classExprMetaModel.propertyMetaModels.add(classExprMetaModel.typePropertyMetaModel);
        conditionalExprMetaModel.conditionPropertyMetaModel = new PropertyMetaModel(conditionalExprMetaModel, "condition", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "condition"), true, false, false, false, false);
        conditionalExprMetaModel.propertyMetaModels.add(conditionalExprMetaModel.conditionPropertyMetaModel);
        conditionalExprMetaModel.elseExprPropertyMetaModel = new PropertyMetaModel(conditionalExprMetaModel, "elseExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "elseExpr"), true, false, false, false, false);
        conditionalExprMetaModel.propertyMetaModels.add(conditionalExprMetaModel.elseExprPropertyMetaModel);
        conditionalExprMetaModel.thenExprPropertyMetaModel = new PropertyMetaModel(conditionalExprMetaModel, "thenExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "thenExpr"), true, false, false, false, false);
        conditionalExprMetaModel.propertyMetaModels.add(conditionalExprMetaModel.thenExprPropertyMetaModel);
        enclosedExprMetaModel.innerPropertyMetaModel = new PropertyMetaModel(enclosedExprMetaModel, "inner", com.github.javaparser.ast.expr.Expression.class, getField(EnclosedExpr.class, "inner"), true, true, false, false, false);
        enclosedExprMetaModel.propertyMetaModels.add(enclosedExprMetaModel.innerPropertyMetaModel);
        fieldAccessExprMetaModel.namePropertyMetaModel = new PropertyMetaModel(fieldAccessExprMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(FieldAccessExpr.class, "name"), true, false, false, false, false);
        fieldAccessExprMetaModel.propertyMetaModels.add(fieldAccessExprMetaModel.namePropertyMetaModel);
        fieldAccessExprMetaModel.scopePropertyMetaModel = new PropertyMetaModel(fieldAccessExprMetaModel, "scope", com.github.javaparser.ast.expr.Expression.class, getField(FieldAccessExpr.class, "scope"), true, true, false, false, false);
        fieldAccessExprMetaModel.propertyMetaModels.add(fieldAccessExprMetaModel.scopePropertyMetaModel);
        fieldAccessExprMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(fieldAccessExprMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(FieldAccessExpr.class, "typeArguments"), true, true, true, false, false);
        fieldAccessExprMetaModel.propertyMetaModels.add(fieldAccessExprMetaModel.typeArgumentsPropertyMetaModel);
        instanceOfExprMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(instanceOfExprMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(InstanceOfExpr.class, "expression"), true, false, false, false, false);
        instanceOfExprMetaModel.propertyMetaModels.add(instanceOfExprMetaModel.expressionPropertyMetaModel);
        instanceOfExprMetaModel.typePropertyMetaModel = new PropertyMetaModel(instanceOfExprMetaModel, "type", com.github.javaparser.ast.type.ReferenceType.class, getField(InstanceOfExpr.class, "type"), true, false, false, false, false);
        instanceOfExprMetaModel.propertyMetaModels.add(instanceOfExprMetaModel.typePropertyMetaModel);
        lambdaExprMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(lambdaExprMetaModel, "body", com.github.javaparser.ast.stmt.Statement.class, getField(LambdaExpr.class, "body"), true, false, false, false, false);
        lambdaExprMetaModel.propertyMetaModels.add(lambdaExprMetaModel.bodyPropertyMetaModel);
        lambdaExprMetaModel.isEnclosingParametersPropertyMetaModel = new PropertyMetaModel(lambdaExprMetaModel, "isEnclosingParameters", boolean.class, getField(LambdaExpr.class, "isEnclosingParameters"), true, false, false, false, false);
        lambdaExprMetaModel.propertyMetaModels.add(lambdaExprMetaModel.isEnclosingParametersPropertyMetaModel);
        lambdaExprMetaModel.parametersPropertyMetaModel = new PropertyMetaModel(lambdaExprMetaModel, "parameters", com.github.javaparser.ast.body.Parameter.class, getField(LambdaExpr.class, "parameters"), true, false, true, false, false);
        lambdaExprMetaModel.propertyMetaModels.add(lambdaExprMetaModel.parametersPropertyMetaModel);
        memberValuePairMetaModel.namePropertyMetaModel = new PropertyMetaModel(memberValuePairMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MemberValuePair.class, "name"), true, false, false, false, false);
        memberValuePairMetaModel.propertyMetaModels.add(memberValuePairMetaModel.namePropertyMetaModel);
        memberValuePairMetaModel.valuePropertyMetaModel = new PropertyMetaModel(memberValuePairMetaModel, "value", com.github.javaparser.ast.expr.Expression.class, getField(MemberValuePair.class, "value"), true, false, false, false, false);
        memberValuePairMetaModel.propertyMetaModels.add(memberValuePairMetaModel.valuePropertyMetaModel);
        methodCallExprMetaModel.argumentsPropertyMetaModel = new PropertyMetaModel(methodCallExprMetaModel, "arguments", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "arguments"), true, false, true, false, false);
        methodCallExprMetaModel.propertyMetaModels.add(methodCallExprMetaModel.argumentsPropertyMetaModel);
        methodCallExprMetaModel.namePropertyMetaModel = new PropertyMetaModel(methodCallExprMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodCallExpr.class, "name"), true, false, false, false, false);
        methodCallExprMetaModel.propertyMetaModels.add(methodCallExprMetaModel.namePropertyMetaModel);
        methodCallExprMetaModel.scopePropertyMetaModel = new PropertyMetaModel(methodCallExprMetaModel, "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "scope"), true, true, false, false, false);
        methodCallExprMetaModel.propertyMetaModels.add(methodCallExprMetaModel.scopePropertyMetaModel);
        methodCallExprMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(methodCallExprMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodCallExpr.class, "typeArguments"), true, true, true, false, false);
        methodCallExprMetaModel.propertyMetaModels.add(methodCallExprMetaModel.typeArgumentsPropertyMetaModel);
        methodReferenceExprMetaModel.identifierPropertyMetaModel = new PropertyMetaModel(methodReferenceExprMetaModel, "identifier", java.lang.String.class, getField(MethodReferenceExpr.class, "identifier"), true, false, false, false, false);
        methodReferenceExprMetaModel.propertyMetaModels.add(methodReferenceExprMetaModel.identifierPropertyMetaModel);
        methodReferenceExprMetaModel.scopePropertyMetaModel = new PropertyMetaModel(methodReferenceExprMetaModel, "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodReferenceExpr.class, "scope"), true, false, false, false, false);
        methodReferenceExprMetaModel.propertyMetaModels.add(methodReferenceExprMetaModel.scopePropertyMetaModel);
        methodReferenceExprMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(methodReferenceExprMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodReferenceExpr.class, "typeArguments"), true, true, true, false, false);
        methodReferenceExprMetaModel.propertyMetaModels.add(methodReferenceExprMetaModel.typeArgumentsPropertyMetaModel);
        nameExprMetaModel.namePropertyMetaModel = new PropertyMetaModel(nameExprMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(NameExpr.class, "name"), true, false, false, false, false);
        nameExprMetaModel.propertyMetaModels.add(nameExprMetaModel.namePropertyMetaModel);
        nameMetaModel.identifierPropertyMetaModel = new PropertyMetaModel(nameMetaModel, "identifier", java.lang.String.class, getField(Name.class, "identifier"), true, false, false, false, false);
        nameMetaModel.propertyMetaModels.add(nameMetaModel.identifierPropertyMetaModel);
        nameMetaModel.qualifierPropertyMetaModel = new PropertyMetaModel(nameMetaModel, "qualifier", com.github.javaparser.ast.expr.Name.class, getField(Name.class, "qualifier"), true, true, false, false, false);
        nameMetaModel.propertyMetaModels.add(nameMetaModel.qualifierPropertyMetaModel);
        normalAnnotationExprMetaModel.pairsPropertyMetaModel = new PropertyMetaModel(normalAnnotationExprMetaModel, "pairs", com.github.javaparser.ast.expr.MemberValuePair.class, getField(NormalAnnotationExpr.class, "pairs"), true, false, true, false, false);
        normalAnnotationExprMetaModel.propertyMetaModels.add(normalAnnotationExprMetaModel.pairsPropertyMetaModel);
        objectCreationExprMetaModel.anonymousClassBodyPropertyMetaModel = new PropertyMetaModel(objectCreationExprMetaModel, "anonymousClassBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(ObjectCreationExpr.class, "anonymousClassBody"), true, true, true, false, true);
        objectCreationExprMetaModel.propertyMetaModels.add(objectCreationExprMetaModel.anonymousClassBodyPropertyMetaModel);
        objectCreationExprMetaModel.argumentsPropertyMetaModel = new PropertyMetaModel(objectCreationExprMetaModel, "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "arguments"), true, false, true, false, false);
        objectCreationExprMetaModel.propertyMetaModels.add(objectCreationExprMetaModel.argumentsPropertyMetaModel);
        objectCreationExprMetaModel.scopePropertyMetaModel = new PropertyMetaModel(objectCreationExprMetaModel, "scope", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "scope"), true, true, false, false, false);
        objectCreationExprMetaModel.propertyMetaModels.add(objectCreationExprMetaModel.scopePropertyMetaModel);
        objectCreationExprMetaModel.typePropertyMetaModel = new PropertyMetaModel(objectCreationExprMetaModel, "type", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ObjectCreationExpr.class, "type"), true, false, false, false, false);
        objectCreationExprMetaModel.propertyMetaModels.add(objectCreationExprMetaModel.typePropertyMetaModel);
        objectCreationExprMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(objectCreationExprMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ObjectCreationExpr.class, "typeArguments"), true, true, true, false, false);
        objectCreationExprMetaModel.propertyMetaModels.add(objectCreationExprMetaModel.typeArgumentsPropertyMetaModel);
        simpleNameMetaModel.identifierPropertyMetaModel = new PropertyMetaModel(simpleNameMetaModel, "identifier", java.lang.String.class, getField(SimpleName.class, "identifier"), true, false, false, false, false);
        simpleNameMetaModel.propertyMetaModels.add(simpleNameMetaModel.identifierPropertyMetaModel);
        singleMemberAnnotationExprMetaModel.memberValuePropertyMetaModel = new PropertyMetaModel(singleMemberAnnotationExprMetaModel, "memberValue", com.github.javaparser.ast.expr.Expression.class, getField(SingleMemberAnnotationExpr.class, "memberValue"), true, false, false, false, false);
        singleMemberAnnotationExprMetaModel.propertyMetaModels.add(singleMemberAnnotationExprMetaModel.memberValuePropertyMetaModel);
        superExprMetaModel.classExprPropertyMetaModel = new PropertyMetaModel(superExprMetaModel, "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(SuperExpr.class, "classExpr"), true, true, false, false, false);
        superExprMetaModel.propertyMetaModels.add(superExprMetaModel.classExprPropertyMetaModel);
        thisExprMetaModel.classExprPropertyMetaModel = new PropertyMetaModel(thisExprMetaModel, "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(ThisExpr.class, "classExpr"), true, true, false, false, false);
        thisExprMetaModel.propertyMetaModels.add(thisExprMetaModel.classExprPropertyMetaModel);
        typeExprMetaModel.typePropertyMetaModel = new PropertyMetaModel(typeExprMetaModel, "type", com.github.javaparser.ast.type.Type.class, getField(TypeExpr.class, "type"), true, false, false, false, false);
        typeExprMetaModel.propertyMetaModels.add(typeExprMetaModel.typePropertyMetaModel);
        unaryExprMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(unaryExprMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(UnaryExpr.class, "expression"), true, false, false, false, false);
        unaryExprMetaModel.propertyMetaModels.add(unaryExprMetaModel.expressionPropertyMetaModel);
        unaryExprMetaModel.operatorPropertyMetaModel = new PropertyMetaModel(unaryExprMetaModel, "operator", com.github.javaparser.ast.expr.UnaryExpr.Operator.class, getField(UnaryExpr.class, "operator"), true, false, false, false, false);
        unaryExprMetaModel.propertyMetaModels.add(unaryExprMetaModel.operatorPropertyMetaModel);
        variableDeclarationExprMetaModel.annotationsPropertyMetaModel = new PropertyMetaModel(variableDeclarationExprMetaModel, "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(VariableDeclarationExpr.class, "annotations"), true, false, true, false, false);
        variableDeclarationExprMetaModel.propertyMetaModels.add(variableDeclarationExprMetaModel.annotationsPropertyMetaModel);
        variableDeclarationExprMetaModel.modifiersPropertyMetaModel = new PropertyMetaModel(variableDeclarationExprMetaModel, "modifiers", com.github.javaparser.ast.Modifier.class, getField(VariableDeclarationExpr.class, "modifiers"), true, false, false, true, false);
        variableDeclarationExprMetaModel.propertyMetaModels.add(variableDeclarationExprMetaModel.modifiersPropertyMetaModel);
        variableDeclarationExprMetaModel.variablesPropertyMetaModel = new PropertyMetaModel(variableDeclarationExprMetaModel, "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(VariableDeclarationExpr.class, "variables"), true, false, true, false, false);
        variableDeclarationExprMetaModel.propertyMetaModels.add(variableDeclarationExprMetaModel.variablesPropertyMetaModel);
        importDeclarationMetaModel.isAsteriskPropertyMetaModel = new PropertyMetaModel(importDeclarationMetaModel, "isAsterisk", boolean.class, getField(ImportDeclaration.class, "isAsterisk"), true, false, false, false, false);
        importDeclarationMetaModel.propertyMetaModels.add(importDeclarationMetaModel.isAsteriskPropertyMetaModel);
        importDeclarationMetaModel.isStaticPropertyMetaModel = new PropertyMetaModel(importDeclarationMetaModel, "isStatic", boolean.class, getField(ImportDeclaration.class, "isStatic"), true, false, false, false, false);
        importDeclarationMetaModel.propertyMetaModels.add(importDeclarationMetaModel.isStaticPropertyMetaModel);
        importDeclarationMetaModel.namePropertyMetaModel = new PropertyMetaModel(importDeclarationMetaModel, "name", com.github.javaparser.ast.expr.Name.class, getField(ImportDeclaration.class, "name"), true, false, false, false, false);
        importDeclarationMetaModel.propertyMetaModels.add(importDeclarationMetaModel.namePropertyMetaModel);
        assertStmtMetaModel.checkPropertyMetaModel = new PropertyMetaModel(assertStmtMetaModel, "check", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "check"), true, false, false, false, false);
        assertStmtMetaModel.propertyMetaModels.add(assertStmtMetaModel.checkPropertyMetaModel);
        assertStmtMetaModel.messagePropertyMetaModel = new PropertyMetaModel(assertStmtMetaModel, "message", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "message"), true, true, false, false, false);
        assertStmtMetaModel.propertyMetaModels.add(assertStmtMetaModel.messagePropertyMetaModel);
        blockStmtMetaModel.statementsPropertyMetaModel = new PropertyMetaModel(blockStmtMetaModel, "statements", com.github.javaparser.ast.stmt.Statement.class, getField(BlockStmt.class, "statements"), true, false, true, false, false);
        blockStmtMetaModel.propertyMetaModels.add(blockStmtMetaModel.statementsPropertyMetaModel);
        breakStmtMetaModel.labelPropertyMetaModel = new PropertyMetaModel(breakStmtMetaModel, "label", com.github.javaparser.ast.expr.SimpleName.class, getField(BreakStmt.class, "label"), true, true, false, false, false);
        breakStmtMetaModel.propertyMetaModels.add(breakStmtMetaModel.labelPropertyMetaModel);
        catchClauseMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(catchClauseMetaModel, "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(CatchClause.class, "body"), true, false, false, false, false);
        catchClauseMetaModel.propertyMetaModels.add(catchClauseMetaModel.bodyPropertyMetaModel);
        catchClauseMetaModel.parameterPropertyMetaModel = new PropertyMetaModel(catchClauseMetaModel, "parameter", com.github.javaparser.ast.body.Parameter.class, getField(CatchClause.class, "parameter"), true, false, false, false, false);
        catchClauseMetaModel.propertyMetaModels.add(catchClauseMetaModel.parameterPropertyMetaModel);
        continueStmtMetaModel.labelPropertyMetaModel = new PropertyMetaModel(continueStmtMetaModel, "label", com.github.javaparser.ast.expr.SimpleName.class, getField(ContinueStmt.class, "label"), true, true, false, false, false);
        continueStmtMetaModel.propertyMetaModels.add(continueStmtMetaModel.labelPropertyMetaModel);
        doStmtMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(doStmtMetaModel, "body", com.github.javaparser.ast.stmt.Statement.class, getField(DoStmt.class, "body"), true, false, false, false, false);
        doStmtMetaModel.propertyMetaModels.add(doStmtMetaModel.bodyPropertyMetaModel);
        doStmtMetaModel.conditionPropertyMetaModel = new PropertyMetaModel(doStmtMetaModel, "condition", com.github.javaparser.ast.expr.Expression.class, getField(DoStmt.class, "condition"), true, false, false, false, false);
        doStmtMetaModel.propertyMetaModels.add(doStmtMetaModel.conditionPropertyMetaModel);
        explicitConstructorInvocationStmtMetaModel.argumentsPropertyMetaModel = new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "arguments"), true, false, true, false, false);
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(explicitConstructorInvocationStmtMetaModel.argumentsPropertyMetaModel);
        explicitConstructorInvocationStmtMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "expression"), true, true, false, false, false);
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(explicitConstructorInvocationStmtMetaModel.expressionPropertyMetaModel);
        explicitConstructorInvocationStmtMetaModel.isThisPropertyMetaModel = new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "isThis", boolean.class, getField(ExplicitConstructorInvocationStmt.class, "isThis"), true, false, false, false, false);
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(explicitConstructorInvocationStmtMetaModel.isThisPropertyMetaModel);
        explicitConstructorInvocationStmtMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(explicitConstructorInvocationStmtMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ExplicitConstructorInvocationStmt.class, "typeArguments"), true, true, true, false, false);
        explicitConstructorInvocationStmtMetaModel.propertyMetaModels.add(explicitConstructorInvocationStmtMetaModel.typeArgumentsPropertyMetaModel);
        expressionStmtMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(expressionStmtMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExpressionStmt.class, "expression"), true, false, false, false, false);
        expressionStmtMetaModel.propertyMetaModels.add(expressionStmtMetaModel.expressionPropertyMetaModel);
        foreachStmtMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(foreachStmtMetaModel, "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForeachStmt.class, "body"), true, false, false, false, false);
        foreachStmtMetaModel.propertyMetaModels.add(foreachStmtMetaModel.bodyPropertyMetaModel);
        foreachStmtMetaModel.iterablePropertyMetaModel = new PropertyMetaModel(foreachStmtMetaModel, "iterable", com.github.javaparser.ast.expr.Expression.class, getField(ForeachStmt.class, "iterable"), true, false, false, false, false);
        foreachStmtMetaModel.propertyMetaModels.add(foreachStmtMetaModel.iterablePropertyMetaModel);
        foreachStmtMetaModel.variablePropertyMetaModel = new PropertyMetaModel(foreachStmtMetaModel, "variable", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(ForeachStmt.class, "variable"), true, false, false, false, false);
        foreachStmtMetaModel.propertyMetaModels.add(foreachStmtMetaModel.variablePropertyMetaModel);
        forStmtMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(forStmtMetaModel, "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForStmt.class, "body"), true, false, false, false, false);
        forStmtMetaModel.propertyMetaModels.add(forStmtMetaModel.bodyPropertyMetaModel);
        forStmtMetaModel.comparePropertyMetaModel = new PropertyMetaModel(forStmtMetaModel, "compare", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "compare"), true, true, false, false, false);
        forStmtMetaModel.propertyMetaModels.add(forStmtMetaModel.comparePropertyMetaModel);
        forStmtMetaModel.initializationPropertyMetaModel = new PropertyMetaModel(forStmtMetaModel, "initialization", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "initialization"), true, false, true, false, false);
        forStmtMetaModel.propertyMetaModels.add(forStmtMetaModel.initializationPropertyMetaModel);
        forStmtMetaModel.updatePropertyMetaModel = new PropertyMetaModel(forStmtMetaModel, "update", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "update"), true, false, true, false, false);
        forStmtMetaModel.propertyMetaModels.add(forStmtMetaModel.updatePropertyMetaModel);
        ifStmtMetaModel.conditionPropertyMetaModel = new PropertyMetaModel(ifStmtMetaModel, "condition", com.github.javaparser.ast.expr.Expression.class, getField(IfStmt.class, "condition"), true, false, false, false, false);
        ifStmtMetaModel.propertyMetaModels.add(ifStmtMetaModel.conditionPropertyMetaModel);
        ifStmtMetaModel.elseStmtPropertyMetaModel = new PropertyMetaModel(ifStmtMetaModel, "elseStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "elseStmt"), true, true, false, false, false);
        ifStmtMetaModel.propertyMetaModels.add(ifStmtMetaModel.elseStmtPropertyMetaModel);
        ifStmtMetaModel.thenStmtPropertyMetaModel = new PropertyMetaModel(ifStmtMetaModel, "thenStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "thenStmt"), true, false, false, false, false);
        ifStmtMetaModel.propertyMetaModels.add(ifStmtMetaModel.thenStmtPropertyMetaModel);
        labeledStmtMetaModel.labelPropertyMetaModel = new PropertyMetaModel(labeledStmtMetaModel, "label", com.github.javaparser.ast.expr.SimpleName.class, getField(LabeledStmt.class, "label"), true, false, false, false, false);
        labeledStmtMetaModel.propertyMetaModels.add(labeledStmtMetaModel.labelPropertyMetaModel);
        labeledStmtMetaModel.statementPropertyMetaModel = new PropertyMetaModel(labeledStmtMetaModel, "statement", com.github.javaparser.ast.stmt.Statement.class, getField(LabeledStmt.class, "statement"), true, false, false, false, false);
        labeledStmtMetaModel.propertyMetaModels.add(labeledStmtMetaModel.statementPropertyMetaModel);
        returnStmtMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(returnStmtMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(ReturnStmt.class, "expression"), true, true, false, false, false);
        returnStmtMetaModel.propertyMetaModels.add(returnStmtMetaModel.expressionPropertyMetaModel);
        switchEntryStmtMetaModel.labelPropertyMetaModel = new PropertyMetaModel(switchEntryStmtMetaModel, "label", com.github.javaparser.ast.expr.Expression.class, getField(SwitchEntryStmt.class, "label"), true, true, false, false, false);
        switchEntryStmtMetaModel.propertyMetaModels.add(switchEntryStmtMetaModel.labelPropertyMetaModel);
        switchEntryStmtMetaModel.statementsPropertyMetaModel = new PropertyMetaModel(switchEntryStmtMetaModel, "statements", com.github.javaparser.ast.stmt.Statement.class, getField(SwitchEntryStmt.class, "statements"), true, false, true, false, false);
        switchEntryStmtMetaModel.propertyMetaModels.add(switchEntryStmtMetaModel.statementsPropertyMetaModel);
        switchStmtMetaModel.entriesPropertyMetaModel = new PropertyMetaModel(switchStmtMetaModel, "entries", com.github.javaparser.ast.stmt.SwitchEntryStmt.class, getField(SwitchStmt.class, "entries"), true, false, true, false, false);
        switchStmtMetaModel.propertyMetaModels.add(switchStmtMetaModel.entriesPropertyMetaModel);
        switchStmtMetaModel.selectorPropertyMetaModel = new PropertyMetaModel(switchStmtMetaModel, "selector", com.github.javaparser.ast.expr.Expression.class, getField(SwitchStmt.class, "selector"), true, false, false, false, false);
        switchStmtMetaModel.propertyMetaModels.add(switchStmtMetaModel.selectorPropertyMetaModel);
        synchronizedStmtMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(synchronizedStmtMetaModel, "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(SynchronizedStmt.class, "body"), true, false, false, false, false);
        synchronizedStmtMetaModel.propertyMetaModels.add(synchronizedStmtMetaModel.bodyPropertyMetaModel);
        synchronizedStmtMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(synchronizedStmtMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(SynchronizedStmt.class, "expression"), true, false, false, false, false);
        synchronizedStmtMetaModel.propertyMetaModels.add(synchronizedStmtMetaModel.expressionPropertyMetaModel);
        throwStmtMetaModel.expressionPropertyMetaModel = new PropertyMetaModel(throwStmtMetaModel, "expression", com.github.javaparser.ast.expr.Expression.class, getField(ThrowStmt.class, "expression"), true, false, false, false, false);
        throwStmtMetaModel.propertyMetaModels.add(throwStmtMetaModel.expressionPropertyMetaModel);
        tryStmtMetaModel.catchClausesPropertyMetaModel = new PropertyMetaModel(tryStmtMetaModel, "catchClauses", com.github.javaparser.ast.stmt.CatchClause.class, getField(TryStmt.class, "catchClauses"), true, false, true, false, false);
        tryStmtMetaModel.propertyMetaModels.add(tryStmtMetaModel.catchClausesPropertyMetaModel);
        tryStmtMetaModel.finallyBlockPropertyMetaModel = new PropertyMetaModel(tryStmtMetaModel, "finallyBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "finallyBlock"), true, true, false, false, false);
        tryStmtMetaModel.propertyMetaModels.add(tryStmtMetaModel.finallyBlockPropertyMetaModel);
        tryStmtMetaModel.resourcesPropertyMetaModel = new PropertyMetaModel(tryStmtMetaModel, "resources", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(TryStmt.class, "resources"), true, false, true, false, false);
        tryStmtMetaModel.propertyMetaModels.add(tryStmtMetaModel.resourcesPropertyMetaModel);
        tryStmtMetaModel.tryBlockPropertyMetaModel = new PropertyMetaModel(tryStmtMetaModel, "tryBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "tryBlock"), true, true, false, false, false);
        tryStmtMetaModel.propertyMetaModels.add(tryStmtMetaModel.tryBlockPropertyMetaModel);
        localClassDeclarationStmtMetaModel.classDeclarationPropertyMetaModel = new PropertyMetaModel(localClassDeclarationStmtMetaModel, "classDeclaration", com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, getField(LocalClassDeclarationStmt.class, "classDeclaration"), true, false, false, false, false);
        localClassDeclarationStmtMetaModel.propertyMetaModels.add(localClassDeclarationStmtMetaModel.classDeclarationPropertyMetaModel);
        whileStmtMetaModel.bodyPropertyMetaModel = new PropertyMetaModel(whileStmtMetaModel, "body", com.github.javaparser.ast.stmt.Statement.class, getField(WhileStmt.class, "body"), true, false, false, false, false);
        whileStmtMetaModel.propertyMetaModels.add(whileStmtMetaModel.bodyPropertyMetaModel);
        whileStmtMetaModel.conditionPropertyMetaModel = new PropertyMetaModel(whileStmtMetaModel, "condition", com.github.javaparser.ast.expr.Expression.class, getField(WhileStmt.class, "condition"), true, false, false, false, false);
        whileStmtMetaModel.propertyMetaModels.add(whileStmtMetaModel.conditionPropertyMetaModel);
        arrayTypeMetaModel.componentTypePropertyMetaModel = new PropertyMetaModel(arrayTypeMetaModel, "componentType", com.github.javaparser.ast.type.Type.class, getField(ArrayType.class, "componentType"), true, false, false, false, false);
        arrayTypeMetaModel.propertyMetaModels.add(arrayTypeMetaModel.componentTypePropertyMetaModel);
        classOrInterfaceTypeMetaModel.namePropertyMetaModel = new PropertyMetaModel(classOrInterfaceTypeMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ClassOrInterfaceType.class, "name"), true, false, false, false, false);
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(classOrInterfaceTypeMetaModel.namePropertyMetaModel);
        classOrInterfaceTypeMetaModel.scopePropertyMetaModel = new PropertyMetaModel(classOrInterfaceTypeMetaModel, "scope", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceType.class, "scope"), true, true, false, false, false);
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(classOrInterfaceTypeMetaModel.scopePropertyMetaModel);
        classOrInterfaceTypeMetaModel.typeArgumentsPropertyMetaModel = new PropertyMetaModel(classOrInterfaceTypeMetaModel, "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ClassOrInterfaceType.class, "typeArguments"), true, true, true, false, false);
        classOrInterfaceTypeMetaModel.propertyMetaModels.add(classOrInterfaceTypeMetaModel.typeArgumentsPropertyMetaModel);
        intersectionTypeMetaModel.elementsPropertyMetaModel = new PropertyMetaModel(intersectionTypeMetaModel, "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(IntersectionType.class, "elements"), true, false, true, false, false);
        intersectionTypeMetaModel.propertyMetaModels.add(intersectionTypeMetaModel.elementsPropertyMetaModel);
        primitiveTypeMetaModel.typePropertyMetaModel = new PropertyMetaModel(primitiveTypeMetaModel, "type", com.github.javaparser.ast.type.PrimitiveType.Primitive.class, getField(PrimitiveType.class, "type"), true, false, false, false, false);
        primitiveTypeMetaModel.propertyMetaModels.add(primitiveTypeMetaModel.typePropertyMetaModel);
        typeParameterMetaModel.namePropertyMetaModel = new PropertyMetaModel(typeParameterMetaModel, "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeParameter.class, "name"), true, false, false, false, false);
        typeParameterMetaModel.propertyMetaModels.add(typeParameterMetaModel.namePropertyMetaModel);
        typeParameterMetaModel.typeBoundPropertyMetaModel = new PropertyMetaModel(typeParameterMetaModel, "typeBound", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(TypeParameter.class, "typeBound"), true, false, true, false, false);
        typeParameterMetaModel.propertyMetaModels.add(typeParameterMetaModel.typeBoundPropertyMetaModel);
        unionTypeMetaModel.elementsPropertyMetaModel = new PropertyMetaModel(unionTypeMetaModel, "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(UnionType.class, "elements"), true, false, true, false, false);
        unionTypeMetaModel.propertyMetaModels.add(unionTypeMetaModel.elementsPropertyMetaModel);
        wildcardTypeMetaModel.extendedTypesPropertyMetaModel = new PropertyMetaModel(wildcardTypeMetaModel, "extendedTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "extendedTypes"), true, true, false, false, false);
        wildcardTypeMetaModel.propertyMetaModels.add(wildcardTypeMetaModel.extendedTypesPropertyMetaModel);
        wildcardTypeMetaModel.superTypesPropertyMetaModel = new PropertyMetaModel(wildcardTypeMetaModel, "superTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "superTypes"), true, true, false, false, false);
        wildcardTypeMetaModel.propertyMetaModels.add(wildcardTypeMetaModel.superTypesPropertyMetaModel);
    }

    public Optional<BaseNodeMetaModel> getClassMetaModel(Class<?> c) {
        for (BaseNodeMetaModel oldClassMetaModel : nodeMetaModels) {
            if (oldClassMetaModel.name.equals(c.getSimpleName())) {
                return Optional.of(oldClassMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (BaseNodeMetaModel classMetaModel : nodeMetaModels) {
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

    public final NodeMetaModel nodeMetaModel = new NodeMetaModel(this, Optional.empty());

    public final BodyDeclarationMetaModel bodyDeclarationMetaModel = new BodyDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final StatementMetaModel statementMetaModel = new StatementMetaModel(this, Optional.of(nodeMetaModel));

    public final ExpressionMetaModel expressionMetaModel = new ExpressionMetaModel(this, Optional.of(nodeMetaModel));

    public final TypeMetaModel typeMetaModel = new TypeMetaModel(this, Optional.of(nodeMetaModel));

    public final AnnotationExprMetaModel annotationExprMetaModel = new AnnotationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final TypeDeclarationMetaModel typeDeclarationMetaModel = new TypeDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final LiteralExprMetaModel literalExprMetaModel = new LiteralExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ReferenceTypeMetaModel referenceTypeMetaModel = new ReferenceTypeMetaModel(this, Optional.of(typeMetaModel));

    public final StringLiteralExprMetaModel stringLiteralExprMetaModel = new StringLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final ArrayCreationLevelMetaModel arrayCreationLevelMetaModel = new ArrayCreationLevelMetaModel(this, Optional.of(nodeMetaModel));

    public final CompilationUnitMetaModel compilationUnitMetaModel = new CompilationUnitMetaModel(this, Optional.of(nodeMetaModel));

    public final PackageDeclarationMetaModel packageDeclarationMetaModel = new PackageDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final AnnotationDeclarationMetaModel annotationDeclarationMetaModel = new AnnotationDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final AnnotationMemberDeclarationMetaModel annotationMemberDeclarationMetaModel = new AnnotationMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassOrInterfaceDeclarationMetaModel classOrInterfaceDeclarationMetaModel = new ClassOrInterfaceDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final ConstructorDeclarationMetaModel constructorDeclarationMetaModel = new ConstructorDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final EmptyMemberDeclarationMetaModel emptyMemberDeclarationMetaModel = new EmptyMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final EnumConstantDeclarationMetaModel enumConstantDeclarationMetaModel = new EnumConstantDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final EnumDeclarationMetaModel enumDeclarationMetaModel = new EnumDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final FieldDeclarationMetaModel fieldDeclarationMetaModel = new FieldDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final InitializerDeclarationMetaModel initializerDeclarationMetaModel = new InitializerDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final MethodDeclarationMetaModel methodDeclarationMetaModel = new MethodDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ParameterMetaModel parameterMetaModel = new ParameterMetaModel(this, Optional.of(nodeMetaModel));

    public final VariableDeclaratorMetaModel variableDeclaratorMetaModel = new VariableDeclaratorMetaModel(this, Optional.of(nodeMetaModel));

    public final CommentMetaModel commentMetaModel = new CommentMetaModel(this, Optional.of(nodeMetaModel));

    public final BlockCommentMetaModel blockCommentMetaModel = new BlockCommentMetaModel(this, Optional.of(commentMetaModel));

    public final JavadocCommentMetaModel javadocCommentMetaModel = new JavadocCommentMetaModel(this, Optional.of(commentMetaModel));

    public final LineCommentMetaModel lineCommentMetaModel = new LineCommentMetaModel(this, Optional.of(commentMetaModel));

    public final ArrayAccessExprMetaModel arrayAccessExprMetaModel = new ArrayAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ArrayCreationExprMetaModel arrayCreationExprMetaModel = new ArrayCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ArrayInitializerExprMetaModel arrayInitializerExprMetaModel = new ArrayInitializerExprMetaModel(this, Optional.of(expressionMetaModel));

    public final AssignExprMetaModel assignExprMetaModel = new AssignExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BinaryExprMetaModel binaryExprMetaModel = new BinaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final BooleanLiteralExprMetaModel booleanLiteralExprMetaModel = new BooleanLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final CastExprMetaModel castExprMetaModel = new CastExprMetaModel(this, Optional.of(expressionMetaModel));

    public final CharLiteralExprMetaModel charLiteralExprMetaModel = new CharLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final ClassExprMetaModel classExprMetaModel = new ClassExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ConditionalExprMetaModel conditionalExprMetaModel = new ConditionalExprMetaModel(this, Optional.of(expressionMetaModel));

    public final DoubleLiteralExprMetaModel doubleLiteralExprMetaModel = new DoubleLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final EnclosedExprMetaModel enclosedExprMetaModel = new EnclosedExprMetaModel(this, Optional.of(expressionMetaModel));

    public final FieldAccessExprMetaModel fieldAccessExprMetaModel = new FieldAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final InstanceOfExprMetaModel instanceOfExprMetaModel = new InstanceOfExprMetaModel(this, Optional.of(expressionMetaModel));

    public final IntegerLiteralExprMetaModel integerLiteralExprMetaModel = new IntegerLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final LambdaExprMetaModel lambdaExprMetaModel = new LambdaExprMetaModel(this, Optional.of(expressionMetaModel));

    public final LongLiteralExprMetaModel longLiteralExprMetaModel = new LongLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final MarkerAnnotationExprMetaModel markerAnnotationExprMetaModel = new MarkerAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final MemberValuePairMetaModel memberValuePairMetaModel = new MemberValuePairMetaModel(this, Optional.of(nodeMetaModel));

    public final MethodCallExprMetaModel methodCallExprMetaModel = new MethodCallExprMetaModel(this, Optional.of(expressionMetaModel));

    public final MethodReferenceExprMetaModel methodReferenceExprMetaModel = new MethodReferenceExprMetaModel(this, Optional.of(expressionMetaModel));

    public final NameExprMetaModel nameExprMetaModel = new NameExprMetaModel(this, Optional.of(expressionMetaModel));

    public final NameMetaModel nameMetaModel = new NameMetaModel(this, Optional.of(nodeMetaModel));

    public final NormalAnnotationExprMetaModel normalAnnotationExprMetaModel = new NormalAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final NullLiteralExprMetaModel nullLiteralExprMetaModel = new NullLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final ObjectCreationExprMetaModel objectCreationExprMetaModel = new ObjectCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final SimpleNameMetaModel simpleNameMetaModel = new SimpleNameMetaModel(this, Optional.of(nodeMetaModel));

    public final SingleMemberAnnotationExprMetaModel singleMemberAnnotationExprMetaModel = new SingleMemberAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final SuperExprMetaModel superExprMetaModel = new SuperExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ThisExprMetaModel thisExprMetaModel = new ThisExprMetaModel(this, Optional.of(expressionMetaModel));

    public final TypeExprMetaModel typeExprMetaModel = new TypeExprMetaModel(this, Optional.of(expressionMetaModel));

    public final UnaryExprMetaModel unaryExprMetaModel = new UnaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final VariableDeclarationExprMetaModel variableDeclarationExprMetaModel = new VariableDeclarationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ImportDeclarationMetaModel importDeclarationMetaModel = new ImportDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final AssertStmtMetaModel assertStmtMetaModel = new AssertStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BlockStmtMetaModel blockStmtMetaModel = new BlockStmtMetaModel(this, Optional.of(statementMetaModel));

    public final BreakStmtMetaModel breakStmtMetaModel = new BreakStmtMetaModel(this, Optional.of(statementMetaModel));

    public final CatchClauseMetaModel catchClauseMetaModel = new CatchClauseMetaModel(this, Optional.of(nodeMetaModel));

    public final ContinueStmtMetaModel continueStmtMetaModel = new ContinueStmtMetaModel(this, Optional.of(statementMetaModel));

    public final DoStmtMetaModel doStmtMetaModel = new DoStmtMetaModel(this, Optional.of(statementMetaModel));

    public final EmptyStmtMetaModel emptyStmtMetaModel = new EmptyStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ExplicitConstructorInvocationStmtMetaModel explicitConstructorInvocationStmtMetaModel = new ExplicitConstructorInvocationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ExpressionStmtMetaModel expressionStmtMetaModel = new ExpressionStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ForeachStmtMetaModel foreachStmtMetaModel = new ForeachStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ForStmtMetaModel forStmtMetaModel = new ForStmtMetaModel(this, Optional.of(statementMetaModel));

    public final IfStmtMetaModel ifStmtMetaModel = new IfStmtMetaModel(this, Optional.of(statementMetaModel));

    public final LabeledStmtMetaModel labeledStmtMetaModel = new LabeledStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ReturnStmtMetaModel returnStmtMetaModel = new ReturnStmtMetaModel(this, Optional.of(statementMetaModel));

    public final SwitchEntryStmtMetaModel switchEntryStmtMetaModel = new SwitchEntryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final SwitchStmtMetaModel switchStmtMetaModel = new SwitchStmtMetaModel(this, Optional.of(statementMetaModel));

    public final SynchronizedStmtMetaModel synchronizedStmtMetaModel = new SynchronizedStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ThrowStmtMetaModel throwStmtMetaModel = new ThrowStmtMetaModel(this, Optional.of(statementMetaModel));

    public final TryStmtMetaModel tryStmtMetaModel = new TryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final LocalClassDeclarationStmtMetaModel localClassDeclarationStmtMetaModel = new LocalClassDeclarationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final WhileStmtMetaModel whileStmtMetaModel = new WhileStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ArrayTypeMetaModel arrayTypeMetaModel = new ArrayTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final ClassOrInterfaceTypeMetaModel classOrInterfaceTypeMetaModel = new ClassOrInterfaceTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final IntersectionTypeMetaModel intersectionTypeMetaModel = new IntersectionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final PrimitiveTypeMetaModel primitiveTypeMetaModel = new PrimitiveTypeMetaModel(this, Optional.of(typeMetaModel));

    public final TypeParameterMetaModel typeParameterMetaModel = new TypeParameterMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final UnionTypeMetaModel unionTypeMetaModel = new UnionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final UnknownTypeMetaModel unknownTypeMetaModel = new UnknownTypeMetaModel(this, Optional.of(typeMetaModel));

    public final VoidTypeMetaModel voidTypeMetaModel = new VoidTypeMetaModel(this, Optional.of(typeMetaModel));

    public final WildcardTypeMetaModel wildcardTypeMetaModel = new WildcardTypeMetaModel(this, Optional.of(typeMetaModel));
}

