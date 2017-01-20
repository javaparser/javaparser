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

    public final List<ClassMetaModel> classMetaModels = new ArrayList<>();

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
        nodeMetaModel.fieldMetaModels.add(new FieldMetaModel(nodeMetaModel, "getComment", "setComment", "comment", com.github.javaparser.ast.comments.Comment.class, getField(Node.class, "comment"), true, false, false, false, false));
        bodyDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(bodyDeclarationMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(BodyDeclaration.class, "annotations"), true, false, true, false, false));
        typeMetaModel.fieldMetaModels.add(new FieldMetaModel(typeMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Type.class, "annotations"), true, false, true, false, false));
        annotationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(annotationExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(AnnotationExpr.class, "name"), true, false, false, false, false));
        typeDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(typeDeclarationMetaModel, "getMembers", "setMembers", "members", com.github.javaparser.ast.body.BodyDeclaration.class, getField(TypeDeclaration.class, "members"), true, false, true, false, true));
        typeDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(typeDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(TypeDeclaration.class, "modifiers"), true, false, false, true, false));
        typeDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(typeDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeDeclaration.class, "name"), true, false, false, false, false));
        stringLiteralExprMetaModel.fieldMetaModels.add(new FieldMetaModel(stringLiteralExprMetaModel, "getValue", "setValue", "value", java.lang.String.class, getField(StringLiteralExpr.class, "value"), true, false, false, false, false));
        arrayCreationLevelMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayCreationLevelMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(ArrayCreationLevel.class, "annotations"), true, false, true, false, false));
        arrayCreationLevelMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayCreationLevelMetaModel, "getDimension", "setDimension", "dimension", com.github.javaparser.ast.expr.Expression.class, getField(ArrayCreationLevel.class, "dimension"), true, true, false, false, false));
        compilationUnitMetaModel.fieldMetaModels.add(new FieldMetaModel(compilationUnitMetaModel, "getImports", "setImports", "imports", com.github.javaparser.ast.ImportDeclaration.class, getField(CompilationUnit.class, "imports"), true, false, true, false, false));
        compilationUnitMetaModel.fieldMetaModels.add(new FieldMetaModel(compilationUnitMetaModel, "getPackageDeclaration", "setPackageDeclaration", "packageDeclaration", com.github.javaparser.ast.PackageDeclaration.class, getField(CompilationUnit.class, "packageDeclaration"), true, true, false, false, false));
        compilationUnitMetaModel.fieldMetaModels.add(new FieldMetaModel(compilationUnitMetaModel, "getTypes", "setTypes", "types", com.github.javaparser.ast.body.TypeDeclaration.class, getField(CompilationUnit.class, "types"), true, false, true, false, true));
        packageDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(packageDeclarationMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(PackageDeclaration.class, "annotations"), true, false, true, false, false));
        packageDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(packageDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(PackageDeclaration.class, "name"), true, false, false, false, false));
        annotationMemberDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(annotationMemberDeclarationMetaModel, "getDefaultValue", "setDefaultValue", "defaultValue", com.github.javaparser.ast.expr.Expression.class, getField(AnnotationMemberDeclaration.class, "defaultValue"), true, true, false, false, false));
        annotationMemberDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(annotationMemberDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(AnnotationMemberDeclaration.class, "modifiers"), true, false, false, true, false));
        annotationMemberDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(annotationMemberDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(AnnotationMemberDeclaration.class, "name"), true, false, false, false, false));
        annotationMemberDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(annotationMemberDeclarationMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(AnnotationMemberDeclaration.class, "type"), true, false, false, false, false));
        classOrInterfaceDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceDeclarationMetaModel, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "extendedTypes"), true, false, true, false, false));
        classOrInterfaceDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceDeclarationMetaModel, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceDeclaration.class, "implementedTypes"), true, false, true, false, false));
        classOrInterfaceDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceDeclarationMetaModel, "isInterface", "setIsInterface", "isInterface", boolean.class, getField(ClassOrInterfaceDeclaration.class, "isInterface"), true, false, false, false, false));
        classOrInterfaceDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ClassOrInterfaceDeclaration.class, "typeParameters"), true, false, true, false, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(ConstructorDeclaration.class, "body"), true, false, false, false, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(ConstructorDeclaration.class, "modifiers"), true, false, false, true, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ConstructorDeclaration.class, "name"), true, false, false, false, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(ConstructorDeclaration.class, "parameters"), true, false, true, false, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(ConstructorDeclaration.class, "thrownExceptions"), true, false, true, false, false));
        constructorDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(constructorDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(ConstructorDeclaration.class, "typeParameters"), true, false, true, false, false));
        enumConstantDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(enumConstantDeclarationMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(EnumConstantDeclaration.class, "arguments"), true, false, true, false, false));
        enumConstantDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(enumConstantDeclarationMetaModel, "getClassBody", "setClassBody", "classBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(EnumConstantDeclaration.class, "classBody"), true, false, true, false, true));
        enumConstantDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(enumConstantDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(EnumConstantDeclaration.class, "name"), true, false, false, false, false));
        enumDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(enumDeclarationMetaModel, "getEntries", "setEntries", "entries", com.github.javaparser.ast.body.EnumConstantDeclaration.class, getField(EnumDeclaration.class, "entries"), true, false, true, false, false));
        enumDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(enumDeclarationMetaModel, "getImplementedTypes", "setImplementedTypes", "implementedTypes", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(EnumDeclaration.class, "implementedTypes"), true, false, true, false, false));
        fieldDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(fieldDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(FieldDeclaration.class, "modifiers"), true, false, false, true, false));
        fieldDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(fieldDeclarationMetaModel, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(FieldDeclaration.class, "variables"), true, false, true, false, false));
        initializerDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(initializerDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(InitializerDeclaration.class, "body"), true, false, false, false, false));
        initializerDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(initializerDeclarationMetaModel, "isStatic", "setIsStatic", "isStatic", boolean.class, getField(InitializerDeclaration.class, "isStatic"), true, false, false, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(MethodDeclaration.class, "body"), true, true, false, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "isDefault", "setIsDefault", "isDefault", boolean.class, getField(MethodDeclaration.class, "isDefault"), true, false, false, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(MethodDeclaration.class, "modifiers"), true, false, false, true, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodDeclaration.class, "name"), true, false, false, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(MethodDeclaration.class, "parameters"), true, false, true, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getThrownExceptions", "setThrownExceptions", "thrownExceptions", com.github.javaparser.ast.type.ReferenceType.class, getField(MethodDeclaration.class, "thrownExceptions"), true, false, true, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(MethodDeclaration.class, "type"), true, false, false, false, false));
        methodDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(methodDeclarationMetaModel, "getTypeParameters", "setTypeParameters", "typeParameters", com.github.javaparser.ast.type.TypeParameter.class, getField(MethodDeclaration.class, "typeParameters"), true, false, true, false, false));
        parameterMetaModel.fieldMetaModels.add(new FieldMetaModel(parameterMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(Parameter.class, "annotations"), true, false, true, false, false));
        parameterMetaModel.fieldMetaModels.add(new FieldMetaModel(parameterMetaModel, "isVarArgs", "setIsVarArgs", "isVarArgs", boolean.class, getField(Parameter.class, "isVarArgs"), true, false, false, false, false));
        parameterMetaModel.fieldMetaModels.add(new FieldMetaModel(parameterMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(Parameter.class, "modifiers"), true, false, false, true, false));
        parameterMetaModel.fieldMetaModels.add(new FieldMetaModel(parameterMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(Parameter.class, "name"), true, false, false, false, false));
        parameterMetaModel.fieldMetaModels.add(new FieldMetaModel(parameterMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(Parameter.class, "type"), true, false, false, false, false));
        variableDeclaratorMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclaratorMetaModel, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.Expression.class, getField(VariableDeclarator.class, "initializer"), true, true, false, false, false));
        variableDeclaratorMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclaratorMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(VariableDeclarator.class, "name"), true, false, false, false, false));
        variableDeclaratorMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclaratorMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(VariableDeclarator.class, "type"), true, false, false, false, false));
        commentMetaModel.fieldMetaModels.add(new FieldMetaModel(commentMetaModel, "getCommentedNode", "setCommentedNode", "commentedNode", com.github.javaparser.ast.Node.class, getField(Comment.class, "commentedNode"), true, true, false, false, false));
        commentMetaModel.fieldMetaModels.add(new FieldMetaModel(commentMetaModel, "getContent", "setContent", "content", java.lang.String.class, getField(Comment.class, "content"), true, false, false, false, false));
        arrayAccessExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayAccessExprMetaModel, "getIndex", "setIndex", "index", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "index"), true, false, false, false, false));
        arrayAccessExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayAccessExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Expression.class, getField(ArrayAccessExpr.class, "name"), true, false, false, false, false));
        arrayCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayCreationExprMetaModel, "getElementType", "setElementType", "elementType", com.github.javaparser.ast.type.Type.class, getField(ArrayCreationExpr.class, "elementType"), true, false, false, false, false));
        arrayCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayCreationExprMetaModel, "getInitializer", "setInitializer", "initializer", com.github.javaparser.ast.expr.ArrayInitializerExpr.class, getField(ArrayCreationExpr.class, "initializer"), true, true, false, false, false));
        arrayCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayCreationExprMetaModel, "getLevels", "setLevels", "levels", com.github.javaparser.ast.ArrayCreationLevel.class, getField(ArrayCreationExpr.class, "levels"), true, false, true, false, false));
        arrayInitializerExprMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayInitializerExprMetaModel, "getValues", "setValues", "values", com.github.javaparser.ast.expr.Expression.class, getField(ArrayInitializerExpr.class, "values"), true, false, true, false, false));
        assignExprMetaModel.fieldMetaModels.add(new FieldMetaModel(assignExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.AssignExpr.Operator.class, getField(AssignExpr.class, "operator"), true, false, false, false, false));
        assignExprMetaModel.fieldMetaModels.add(new FieldMetaModel(assignExprMetaModel, "getTarget", "setTarget", "target", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "target"), true, false, false, false, false));
        assignExprMetaModel.fieldMetaModels.add(new FieldMetaModel(assignExprMetaModel, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField(AssignExpr.class, "value"), true, false, false, false, false));
        binaryExprMetaModel.fieldMetaModels.add(new FieldMetaModel(binaryExprMetaModel, "getLeft", "setLeft", "left", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "left"), true, false, false, false, false));
        binaryExprMetaModel.fieldMetaModels.add(new FieldMetaModel(binaryExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.BinaryExpr.Operator.class, getField(BinaryExpr.class, "operator"), true, false, false, false, false));
        binaryExprMetaModel.fieldMetaModels.add(new FieldMetaModel(binaryExprMetaModel, "getRight", "setRight", "right", com.github.javaparser.ast.expr.Expression.class, getField(BinaryExpr.class, "right"), true, false, false, false, false));
        booleanLiteralExprMetaModel.fieldMetaModels.add(new FieldMetaModel(booleanLiteralExprMetaModel, "getValue", "setValue", "value", boolean.class, getField(BooleanLiteralExpr.class, "value"), true, false, false, false, false));
        castExprMetaModel.fieldMetaModels.add(new FieldMetaModel(castExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(CastExpr.class, "expression"), true, false, false, false, false));
        castExprMetaModel.fieldMetaModels.add(new FieldMetaModel(castExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(CastExpr.class, "type"), true, false, false, false, false));
        classExprMetaModel.fieldMetaModels.add(new FieldMetaModel(classExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(ClassExpr.class, "type"), true, false, false, false, false));
        conditionalExprMetaModel.fieldMetaModels.add(new FieldMetaModel(conditionalExprMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "condition"), true, false, false, false, false));
        conditionalExprMetaModel.fieldMetaModels.add(new FieldMetaModel(conditionalExprMetaModel, "getElseExpr", "setElseExpr", "elseExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "elseExpr"), true, false, false, false, false));
        conditionalExprMetaModel.fieldMetaModels.add(new FieldMetaModel(conditionalExprMetaModel, "getThenExpr", "setThenExpr", "thenExpr", com.github.javaparser.ast.expr.Expression.class, getField(ConditionalExpr.class, "thenExpr"), true, false, false, false, false));
        enclosedExprMetaModel.fieldMetaModels.add(new FieldMetaModel(enclosedExprMetaModel, "getInner", "setInner", "inner", com.github.javaparser.ast.expr.Expression.class, getField(EnclosedExpr.class, "inner"), true, true, false, false, false));
        fieldAccessExprMetaModel.fieldMetaModels.add(new FieldMetaModel(fieldAccessExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(FieldAccessExpr.class, "name"), true, false, false, false, false));
        fieldAccessExprMetaModel.fieldMetaModels.add(new FieldMetaModel(fieldAccessExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(FieldAccessExpr.class, "scope"), true, true, false, false, false));
        fieldAccessExprMetaModel.fieldMetaModels.add(new FieldMetaModel(fieldAccessExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(FieldAccessExpr.class, "typeArguments"), true, true, true, false, false));
        instanceOfExprMetaModel.fieldMetaModels.add(new FieldMetaModel(instanceOfExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(InstanceOfExpr.class, "expression"), true, false, false, false, false));
        instanceOfExprMetaModel.fieldMetaModels.add(new FieldMetaModel(instanceOfExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.ReferenceType.class, getField(InstanceOfExpr.class, "type"), true, false, false, false, false));
        lambdaExprMetaModel.fieldMetaModels.add(new FieldMetaModel(lambdaExprMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(LambdaExpr.class, "body"), true, false, false, false, false));
        lambdaExprMetaModel.fieldMetaModels.add(new FieldMetaModel(lambdaExprMetaModel, "isEnclosingParameters", "setIsEnclosingParameters", "isEnclosingParameters", boolean.class, getField(LambdaExpr.class, "isEnclosingParameters"), true, false, false, false, false));
        lambdaExprMetaModel.fieldMetaModels.add(new FieldMetaModel(lambdaExprMetaModel, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField(LambdaExpr.class, "parameters"), true, false, true, false, false));
        memberValuePairMetaModel.fieldMetaModels.add(new FieldMetaModel(memberValuePairMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MemberValuePair.class, "name"), true, false, false, false, false));
        memberValuePairMetaModel.fieldMetaModels.add(new FieldMetaModel(memberValuePairMetaModel, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField(MemberValuePair.class, "value"), true, false, false, false, false));
        methodCallExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodCallExprMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "arguments"), true, false, true, false, false));
        methodCallExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodCallExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(MethodCallExpr.class, "name"), true, false, false, false, false));
        methodCallExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodCallExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodCallExpr.class, "scope"), true, true, false, false, false));
        methodCallExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodCallExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodCallExpr.class, "typeArguments"), true, true, true, false, false));
        methodReferenceExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodReferenceExprMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(MethodReferenceExpr.class, "identifier"), true, false, false, false, false));
        methodReferenceExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodReferenceExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(MethodReferenceExpr.class, "scope"), true, false, false, false, false));
        methodReferenceExprMetaModel.fieldMetaModels.add(new FieldMetaModel(methodReferenceExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(MethodReferenceExpr.class, "typeArguments"), true, true, true, false, false));
        nameExprMetaModel.fieldMetaModels.add(new FieldMetaModel(nameExprMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(NameExpr.class, "name"), true, false, false, false, false));
        nameMetaModel.fieldMetaModels.add(new FieldMetaModel(nameMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(Name.class, "identifier"), true, false, false, false, false));
        nameMetaModel.fieldMetaModels.add(new FieldMetaModel(nameMetaModel, "getQualifier", "setQualifier", "qualifier", com.github.javaparser.ast.expr.Name.class, getField(Name.class, "qualifier"), true, true, false, false, false));
        normalAnnotationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(normalAnnotationExprMetaModel, "getPairs", "setPairs", "pairs", com.github.javaparser.ast.expr.MemberValuePair.class, getField(NormalAnnotationExpr.class, "pairs"), true, false, true, false, false));
        objectCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(objectCreationExprMetaModel, "getAnonymousClassBody", "setAnonymousClassBody", "anonymousClassBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField(ObjectCreationExpr.class, "anonymousClassBody"), true, true, true, false, true));
        objectCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(objectCreationExprMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "arguments"), true, false, true, false, false));
        objectCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(objectCreationExprMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField(ObjectCreationExpr.class, "scope"), true, true, false, false, false));
        objectCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(objectCreationExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ObjectCreationExpr.class, "type"), true, false, false, false, false));
        objectCreationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(objectCreationExprMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ObjectCreationExpr.class, "typeArguments"), true, true, true, false, false));
        simpleNameMetaModel.fieldMetaModels.add(new FieldMetaModel(simpleNameMetaModel, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField(SimpleName.class, "identifier"), true, false, false, false, false));
        singleMemberAnnotationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(singleMemberAnnotationExprMetaModel, "getMemberValue", "setMemberValue", "memberValue", com.github.javaparser.ast.expr.Expression.class, getField(SingleMemberAnnotationExpr.class, "memberValue"), true, false, false, false, false));
        superExprMetaModel.fieldMetaModels.add(new FieldMetaModel(superExprMetaModel, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(SuperExpr.class, "classExpr"), true, true, false, false, false));
        thisExprMetaModel.fieldMetaModels.add(new FieldMetaModel(thisExprMetaModel, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField(ThisExpr.class, "classExpr"), true, true, false, false, false));
        typeExprMetaModel.fieldMetaModels.add(new FieldMetaModel(typeExprMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField(TypeExpr.class, "type"), true, false, false, false, false));
        unaryExprMetaModel.fieldMetaModels.add(new FieldMetaModel(unaryExprMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(UnaryExpr.class, "expression"), true, false, false, false, false));
        unaryExprMetaModel.fieldMetaModels.add(new FieldMetaModel(unaryExprMetaModel, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.UnaryExpr.Operator.class, getField(UnaryExpr.class, "operator"), true, false, false, false, false));
        variableDeclarationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclarationExprMetaModel, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, getField(VariableDeclarationExpr.class, "annotations"), true, false, true, false, false));
        variableDeclarationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclarationExprMetaModel, "getModifiers", "setModifiers", "modifiers", com.github.javaparser.ast.Modifier.class, getField(VariableDeclarationExpr.class, "modifiers"), true, false, false, true, false));
        variableDeclarationExprMetaModel.fieldMetaModels.add(new FieldMetaModel(variableDeclarationExprMetaModel, "getVariables", "setVariables", "variables", com.github.javaparser.ast.body.VariableDeclarator.class, getField(VariableDeclarationExpr.class, "variables"), true, false, true, false, false));
        importDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(importDeclarationMetaModel, "isAsterisk", "setIsAsterisk", "isAsterisk", boolean.class, getField(ImportDeclaration.class, "isAsterisk"), true, false, false, false, false));
        importDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(importDeclarationMetaModel, "isStatic", "setIsStatic", "isStatic", boolean.class, getField(ImportDeclaration.class, "isStatic"), true, false, false, false, false));
        importDeclarationMetaModel.fieldMetaModels.add(new FieldMetaModel(importDeclarationMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, getField(ImportDeclaration.class, "name"), true, false, false, false, false));
        assertStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(assertStmtMetaModel, "getCheck", "setCheck", "check", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "check"), true, false, false, false, false));
        assertStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(assertStmtMetaModel, "getMessage", "setMessage", "message", com.github.javaparser.ast.expr.Expression.class, getField(AssertStmt.class, "message"), true, true, false, false, false));
        blockStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(blockStmtMetaModel, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, getField(BlockStmt.class, "statements"), true, false, true, false, false));
        breakStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(breakStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(BreakStmt.class, "label"), true, true, false, false, false));
        catchClauseMetaModel.fieldMetaModels.add(new FieldMetaModel(catchClauseMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(CatchClause.class, "body"), true, false, false, false, false));
        catchClauseMetaModel.fieldMetaModels.add(new FieldMetaModel(catchClauseMetaModel, "getParameter", "setParameter", "parameter", com.github.javaparser.ast.body.Parameter.class, getField(CatchClause.class, "parameter"), true, false, false, false, false));
        continueStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(continueStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(ContinueStmt.class, "label"), true, true, false, false, false));
        doStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(doStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(DoStmt.class, "body"), true, false, false, false, false));
        doStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(doStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(DoStmt.class, "condition"), true, false, false, false, false));
        explicitConstructorInvocationStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(explicitConstructorInvocationStmtMetaModel, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "arguments"), true, false, true, false, false));
        explicitConstructorInvocationStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(explicitConstructorInvocationStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExplicitConstructorInvocationStmt.class, "expression"), true, true, false, false, false));
        explicitConstructorInvocationStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(explicitConstructorInvocationStmtMetaModel, "isThis", "setIsThis", "isThis", boolean.class, getField(ExplicitConstructorInvocationStmt.class, "isThis"), true, false, false, false, false));
        explicitConstructorInvocationStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(explicitConstructorInvocationStmtMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ExplicitConstructorInvocationStmt.class, "typeArguments"), true, true, true, false, false));
        expressionStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(expressionStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ExpressionStmt.class, "expression"), true, false, false, false, false));
        foreachStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(foreachStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForeachStmt.class, "body"), true, false, false, false, false));
        foreachStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(foreachStmtMetaModel, "getIterable", "setIterable", "iterable", com.github.javaparser.ast.expr.Expression.class, getField(ForeachStmt.class, "iterable"), true, false, false, false, false));
        foreachStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(foreachStmtMetaModel, "getVariable", "setVariable", "variable", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(ForeachStmt.class, "variable"), true, false, false, false, false));
        forStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(forStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(ForStmt.class, "body"), true, false, false, false, false));
        forStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(forStmtMetaModel, "getCompare", "setCompare", "compare", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "compare"), true, true, false, false, false));
        forStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(forStmtMetaModel, "getInitialization", "setInitialization", "initialization", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "initialization"), true, false, true, false, false));
        forStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(forStmtMetaModel, "getUpdate", "setUpdate", "update", com.github.javaparser.ast.expr.Expression.class, getField(ForStmt.class, "update"), true, false, true, false, false));
        ifStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(ifStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(IfStmt.class, "condition"), true, false, false, false, false));
        ifStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(ifStmtMetaModel, "getElseStmt", "setElseStmt", "elseStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "elseStmt"), true, true, false, false, false));
        ifStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(ifStmtMetaModel, "getThenStmt", "setThenStmt", "thenStmt", com.github.javaparser.ast.stmt.Statement.class, getField(IfStmt.class, "thenStmt"), true, false, false, false, false));
        labeledStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(labeledStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.SimpleName.class, getField(LabeledStmt.class, "label"), true, false, false, false, false));
        labeledStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(labeledStmtMetaModel, "getStatement", "setStatement", "statement", com.github.javaparser.ast.stmt.Statement.class, getField(LabeledStmt.class, "statement"), true, false, false, false, false));
        returnStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(returnStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ReturnStmt.class, "expression"), true, true, false, false, false));
        switchEntryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(switchEntryStmtMetaModel, "getLabel", "setLabel", "label", com.github.javaparser.ast.expr.Expression.class, getField(SwitchEntryStmt.class, "label"), true, true, false, false, false));
        switchEntryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(switchEntryStmtMetaModel, "getStatements", "setStatements", "statements", com.github.javaparser.ast.stmt.Statement.class, getField(SwitchEntryStmt.class, "statements"), true, false, true, false, false));
        switchStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(switchStmtMetaModel, "getEntries", "setEntries", "entries", com.github.javaparser.ast.stmt.SwitchEntryStmt.class, getField(SwitchStmt.class, "entries"), true, false, true, false, false));
        switchStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(switchStmtMetaModel, "getSelector", "setSelector", "selector", com.github.javaparser.ast.expr.Expression.class, getField(SwitchStmt.class, "selector"), true, false, false, false, false));
        synchronizedStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(synchronizedStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField(SynchronizedStmt.class, "body"), true, false, false, false, false));
        synchronizedStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(synchronizedStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(SynchronizedStmt.class, "expression"), true, false, false, false, false));
        throwStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(throwStmtMetaModel, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField(ThrowStmt.class, "expression"), true, false, false, false, false));
        tryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(tryStmtMetaModel, "getCatchClauses", "setCatchClauses", "catchClauses", com.github.javaparser.ast.stmt.CatchClause.class, getField(TryStmt.class, "catchClauses"), true, false, true, false, false));
        tryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(tryStmtMetaModel, "getFinallyBlock", "setFinallyBlock", "finallyBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "finallyBlock"), true, true, false, false, false));
        tryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(tryStmtMetaModel, "getResources", "setResources", "resources", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField(TryStmt.class, "resources"), true, false, true, false, false));
        tryStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(tryStmtMetaModel, "getTryBlock", "setTryBlock", "tryBlock", com.github.javaparser.ast.stmt.BlockStmt.class, getField(TryStmt.class, "tryBlock"), true, true, false, false, false));
        localClassDeclarationStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(localClassDeclarationStmtMetaModel, "getClassDeclaration", "setClassDeclaration", "classDeclaration", com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, getField(LocalClassDeclarationStmt.class, "classDeclaration"), true, false, false, false, false));
        whileStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(whileStmtMetaModel, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField(WhileStmt.class, "body"), true, false, false, false, false));
        whileStmtMetaModel.fieldMetaModels.add(new FieldMetaModel(whileStmtMetaModel, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField(WhileStmt.class, "condition"), true, false, false, false, false));
        arrayTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(arrayTypeMetaModel, "getComponentType", "setComponentType", "componentType", com.github.javaparser.ast.type.Type.class, getField(ArrayType.class, "componentType"), true, false, false, false, false));
        classOrInterfaceTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceTypeMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(ClassOrInterfaceType.class, "name"), true, false, false, false, false));
        classOrInterfaceTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceTypeMetaModel, "getScope", "setScope", "scope", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(ClassOrInterfaceType.class, "scope"), true, true, false, false, false));
        classOrInterfaceTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(classOrInterfaceTypeMetaModel, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField(ClassOrInterfaceType.class, "typeArguments"), true, true, true, false, false));
        intersectionTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(intersectionTypeMetaModel, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(IntersectionType.class, "elements"), true, false, true, false, false));
        primitiveTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(primitiveTypeMetaModel, "getType", "setType", "type", com.github.javaparser.ast.type.PrimitiveType.Primitive.class, getField(PrimitiveType.class, "type"), true, false, false, false, false));
        typeParameterMetaModel.fieldMetaModels.add(new FieldMetaModel(typeParameterMetaModel, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField(TypeParameter.class, "name"), true, false, false, false, false));
        typeParameterMetaModel.fieldMetaModels.add(new FieldMetaModel(typeParameterMetaModel, "getTypeBound", "setTypeBound", "typeBound", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField(TypeParameter.class, "typeBound"), true, false, true, false, false));
        unionTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(unionTypeMetaModel, "getElements", "setElements", "elements", com.github.javaparser.ast.type.ReferenceType.class, getField(UnionType.class, "elements"), true, false, true, false, false));
        wildcardTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(wildcardTypeMetaModel, "getExtendedTypes", "setExtendedTypes", "extendedTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "extendedTypes"), true, true, false, false, false));
        wildcardTypeMetaModel.fieldMetaModels.add(new FieldMetaModel(wildcardTypeMetaModel, "getSuperTypes", "setSuperTypes", "superTypes", com.github.javaparser.ast.type.ReferenceType.class, getField(WildcardType.class, "superTypes"), true, true, false, false, false));
    }

    public Optional<ClassMetaModel> getClassMetaModel(Class<?> c) {
        for (ClassMetaModel oldClassMetaModel : classMetaModels) {
            if (oldClassMetaModel.name.equals(c.getSimpleName())) {
                return Optional.of(oldClassMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (ClassMetaModel classMetaModel : classMetaModels) {
            b.append(classMetaModel).append("\n");
            for (FieldMetaModel fieldMetaModel : classMetaModel.fieldMetaModels) {
                b.append("\t").append(fieldMetaModel).append("\n");
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

    public final ClassMetaModel nodeListMetaModel = new NodeListMetaModel(this, Optional.empty());

    public final ClassMetaModel nodeMetaModel = new NodeMetaModel(this, Optional.empty());

    public final ClassMetaModel bodyDeclarationMetaModel = new BodyDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel statementMetaModel = new StatementMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel expressionMetaModel = new ExpressionMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel typeMetaModel = new TypeMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel annotationExprMetaModel = new AnnotationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel typeDeclarationMetaModel = new TypeDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel literalExprMetaModel = new LiteralExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel referenceTypeMetaModel = new ReferenceTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel stringLiteralExprMetaModel = new StringLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final ClassMetaModel arrayCreationLevelMetaModel = new ArrayCreationLevelMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel compilationUnitMetaModel = new CompilationUnitMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel packageDeclarationMetaModel = new PackageDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel annotationDeclarationMetaModel = new AnnotationDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final ClassMetaModel annotationMemberDeclarationMetaModel = new AnnotationMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel classOrInterfaceDeclarationMetaModel = new ClassOrInterfaceDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final ClassMetaModel constructorDeclarationMetaModel = new ConstructorDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel emptyMemberDeclarationMetaModel = new EmptyMemberDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel enumConstantDeclarationMetaModel = new EnumConstantDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel enumDeclarationMetaModel = new EnumDeclarationMetaModel(this, Optional.of(typeDeclarationMetaModel));

    public final ClassMetaModel fieldDeclarationMetaModel = new FieldDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel initializerDeclarationMetaModel = new InitializerDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel methodDeclarationMetaModel = new MethodDeclarationMetaModel(this, Optional.of(bodyDeclarationMetaModel));

    public final ClassMetaModel parameterMetaModel = new ParameterMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel variableDeclaratorMetaModel = new VariableDeclaratorMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel commentMetaModel = new CommentMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel blockCommentMetaModel = new BlockCommentMetaModel(this, Optional.of(commentMetaModel));

    public final ClassMetaModel javadocCommentMetaModel = new JavadocCommentMetaModel(this, Optional.of(commentMetaModel));

    public final ClassMetaModel lineCommentMetaModel = new LineCommentMetaModel(this, Optional.of(commentMetaModel));

    public final ClassMetaModel arrayAccessExprMetaModel = new ArrayAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel arrayCreationExprMetaModel = new ArrayCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel arrayInitializerExprMetaModel = new ArrayInitializerExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel assignExprMetaModel = new AssignExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel binaryExprMetaModel = new BinaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel booleanLiteralExprMetaModel = new BooleanLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final ClassMetaModel castExprMetaModel = new CastExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel charLiteralExprMetaModel = new CharLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final ClassMetaModel classExprMetaModel = new ClassExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel conditionalExprMetaModel = new ConditionalExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel doubleLiteralExprMetaModel = new DoubleLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final ClassMetaModel enclosedExprMetaModel = new EnclosedExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel fieldAccessExprMetaModel = new FieldAccessExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel instanceOfExprMetaModel = new InstanceOfExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel integerLiteralExprMetaModel = new IntegerLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final ClassMetaModel lambdaExprMetaModel = new LambdaExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel longLiteralExprMetaModel = new LongLiteralExprMetaModel(this, Optional.of(stringLiteralExprMetaModel));

    public final ClassMetaModel markerAnnotationExprMetaModel = new MarkerAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final ClassMetaModel memberValuePairMetaModel = new MemberValuePairMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel methodCallExprMetaModel = new MethodCallExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel methodReferenceExprMetaModel = new MethodReferenceExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel nameExprMetaModel = new NameExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel nameMetaModel = new NameMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel normalAnnotationExprMetaModel = new NormalAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final ClassMetaModel nullLiteralExprMetaModel = new NullLiteralExprMetaModel(this, Optional.of(literalExprMetaModel));

    public final ClassMetaModel objectCreationExprMetaModel = new ObjectCreationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel simpleNameMetaModel = new SimpleNameMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel singleMemberAnnotationExprMetaModel = new SingleMemberAnnotationExprMetaModel(this, Optional.of(annotationExprMetaModel));

    public final ClassMetaModel superExprMetaModel = new SuperExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel thisExprMetaModel = new ThisExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel typeExprMetaModel = new TypeExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel unaryExprMetaModel = new UnaryExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel variableDeclarationExprMetaModel = new VariableDeclarationExprMetaModel(this, Optional.of(expressionMetaModel));

    public final ClassMetaModel importDeclarationMetaModel = new ImportDeclarationMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel assertStmtMetaModel = new AssertStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel blockStmtMetaModel = new BlockStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel breakStmtMetaModel = new BreakStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel catchClauseMetaModel = new CatchClauseMetaModel(this, Optional.of(nodeMetaModel));

    public final ClassMetaModel continueStmtMetaModel = new ContinueStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel doStmtMetaModel = new DoStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel emptyStmtMetaModel = new EmptyStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel explicitConstructorInvocationStmtMetaModel = new ExplicitConstructorInvocationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel expressionStmtMetaModel = new ExpressionStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel foreachStmtMetaModel = new ForeachStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel forStmtMetaModel = new ForStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel ifStmtMetaModel = new IfStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel labeledStmtMetaModel = new LabeledStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel returnStmtMetaModel = new ReturnStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel switchEntryStmtMetaModel = new SwitchEntryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel switchStmtMetaModel = new SwitchStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel synchronizedStmtMetaModel = new SynchronizedStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel throwStmtMetaModel = new ThrowStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel tryStmtMetaModel = new TryStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel localClassDeclarationStmtMetaModel = new LocalClassDeclarationStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel whileStmtMetaModel = new WhileStmtMetaModel(this, Optional.of(statementMetaModel));

    public final ClassMetaModel arrayTypeMetaModel = new ArrayTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final ClassMetaModel classOrInterfaceTypeMetaModel = new ClassOrInterfaceTypeMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final ClassMetaModel intersectionTypeMetaModel = new IntersectionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel primitiveTypeMetaModel = new PrimitiveTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel typeParameterMetaModel = new TypeParameterMetaModel(this, Optional.of(referenceTypeMetaModel));

    public final ClassMetaModel unionTypeMetaModel = new UnionTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel unknownTypeMetaModel = new UnknownTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel voidTypeMetaModel = new VoidTypeMetaModel(this, Optional.of(typeMetaModel));

    public final ClassMetaModel wildcardTypeMetaModel = new WildcardTypeMetaModel(this, Optional.of(typeMetaModel));
}

