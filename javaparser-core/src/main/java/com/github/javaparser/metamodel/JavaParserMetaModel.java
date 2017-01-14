package com.github.javaparser.metamodel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The model contains meta-data about all nodes in the AST.
 * You can base source code generators on it.
 */
public class JavaParserMetaModel {

    private List<ClassMetaModel> classMetaModels = new ArrayList<>();

    public JavaParserMetaModel() {
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
        classMetaModels.add(nameMetaModel);
        classMetaModels.add(nameExprMetaModel);
        classMetaModels.add(nodeMetaModel);
        classMetaModels.add(nodeListMetaModel);
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
        classMetaModels.add(typeMetaModel);
        classMetaModels.add(typeDeclarationMetaModel);
        classMetaModels.add(typeExprMetaModel);
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

    public List<ClassMetaModel> getClassMetaModels() {
        return classMetaModels;
    }

    public Optional<ClassMetaModel> getClassMetaModel(Class<?> c) {
        for (ClassMetaModel oldClassMetaModel : classMetaModels) {
            if (oldClassMetaModel.className.equals(c.getSimpleName())) {
                return Optional.of(oldClassMetaModel);
            }
        }
        return Optional.empty();
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        for (ClassMetaModel oldClassMetaModel : getClassMetaModels()) {
            b.append(oldClassMetaModel).append("\n");
            for (FieldMetaModel oldFieldMetaModel : oldClassMetaModel.fieldMetaModels) {
                b.append("\t").append(oldFieldMetaModel).append("\n");
            }
        }
        return b.toString();
    }

    public final ClassMetaModel annotationDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel annotationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel annotationMemberDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel arrayAccessExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel arrayCreationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel arrayCreationLevelMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel arrayInitializerExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel arrayTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel assertStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel assignExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel binaryExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel blockCommentMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel blockStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel bodyDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel booleanLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel breakStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel castExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel catchClauseMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel charLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel classExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel classOrInterfaceDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel classOrInterfaceTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel commentMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel compilationUnitMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel conditionalExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel constructorDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel continueStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel doStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel doubleLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel emptyMemberDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel emptyStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel enclosedExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel enumConstantDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel enumDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel explicitConstructorInvocationStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel expressionMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel expressionStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel fieldAccessExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel fieldDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel forStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel foreachStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel ifStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel importDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel initializerDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel instanceOfExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel integerLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel intersectionTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel javadocCommentMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel labeledStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel lambdaExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel lineCommentMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel literalExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel localClassDeclarationStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel longLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel markerAnnotationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel memberValuePairMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel methodCallExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel methodDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel methodReferenceExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel nameMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel nameExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel nodeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel nodeListMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel normalAnnotationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel nullLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel objectCreationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel packageDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel parameterMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel primitiveTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel referenceTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel returnStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel simpleNameMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel singleMemberAnnotationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel statementMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel stringLiteralExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel superExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel switchEntryStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel switchStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel synchronizedStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel thisExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel throwStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel tryStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel typeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel typeDeclarationMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel typeExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel typeParameterMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel unaryExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel unionTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel unknownTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel variableDeclarationExprMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel variableDeclaratorMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel voidTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel whileStmtMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);

    public final ClassMetaModel wildcardTypeMetaModel = new ClassMetaModel(null, this, null, null, null, null, false);
}

