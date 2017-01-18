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

    public List<ClassMetaModel> getClassMetaModels() {
        return classMetaModels;
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
        for (ClassMetaModel oldClassMetaModel : getClassMetaModels()) {
            b.append(oldClassMetaModel).append("\n");
            for (FieldMetaModel oldFieldMetaModel : oldClassMetaModel.fieldMetaModels) {
                b.append("\t").append(oldFieldMetaModel).append("\n");
            }
        }
        return b.toString();
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

