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

    public final ClassMetaModel annotationDeclarationMetaModel = new AnnotationDeclarationMetaModel(this);

    public final ClassMetaModel annotationExprMetaModel = new AnnotationExprMetaModel(this);

    public final ClassMetaModel annotationMemberDeclarationMetaModel = new AnnotationMemberDeclarationMetaModel(this);

    public final ClassMetaModel arrayAccessExprMetaModel = new ArrayAccessExprMetaModel(this);

    public final ClassMetaModel arrayCreationExprMetaModel = new ArrayCreationExprMetaModel(this);

    public final ClassMetaModel arrayCreationLevelMetaModel = new ArrayCreationLevelMetaModel(this);

    public final ClassMetaModel arrayInitializerExprMetaModel = new ArrayInitializerExprMetaModel(this);

    public final ClassMetaModel arrayTypeMetaModel = new ArrayTypeMetaModel(this);

    public final ClassMetaModel assertStmtMetaModel = new AssertStmtMetaModel(this);

    public final ClassMetaModel assignExprMetaModel = new AssignExprMetaModel(this);

    public final ClassMetaModel binaryExprMetaModel = new BinaryExprMetaModel(this);

    public final ClassMetaModel blockCommentMetaModel = new BlockCommentMetaModel(this);

    public final ClassMetaModel blockStmtMetaModel = new BlockStmtMetaModel(this);

    public final ClassMetaModel bodyDeclarationMetaModel = new BodyDeclarationMetaModel(this);

    public final ClassMetaModel booleanLiteralExprMetaModel = new BooleanLiteralExprMetaModel(this);

    public final ClassMetaModel breakStmtMetaModel = new BreakStmtMetaModel(this);

    public final ClassMetaModel castExprMetaModel = new CastExprMetaModel(this);

    public final ClassMetaModel catchClauseMetaModel = new CatchClauseMetaModel(this);

    public final ClassMetaModel charLiteralExprMetaModel = new CharLiteralExprMetaModel(this);

    public final ClassMetaModel classExprMetaModel = new ClassExprMetaModel(this);

    public final ClassMetaModel classOrInterfaceDeclarationMetaModel = new ClassOrInterfaceDeclarationMetaModel(this);

    public final ClassMetaModel classOrInterfaceTypeMetaModel = new ClassOrInterfaceTypeMetaModel(this);

    public final ClassMetaModel commentMetaModel = new CommentMetaModel(this);

    public final ClassMetaModel compilationUnitMetaModel = new CompilationUnitMetaModel(this);

    public final ClassMetaModel conditionalExprMetaModel = new ConditionalExprMetaModel(this);

    public final ClassMetaModel constructorDeclarationMetaModel = new ConstructorDeclarationMetaModel(this);

    public final ClassMetaModel continueStmtMetaModel = new ContinueStmtMetaModel(this);

    public final ClassMetaModel doStmtMetaModel = new DoStmtMetaModel(this);

    public final ClassMetaModel doubleLiteralExprMetaModel = new DoubleLiteralExprMetaModel(this);

    public final ClassMetaModel emptyMemberDeclarationMetaModel = new EmptyMemberDeclarationMetaModel(this);

    public final ClassMetaModel emptyStmtMetaModel = new EmptyStmtMetaModel(this);

    public final ClassMetaModel enclosedExprMetaModel = new EnclosedExprMetaModel(this);

    public final ClassMetaModel enumConstantDeclarationMetaModel = new EnumConstantDeclarationMetaModel(this);

    public final ClassMetaModel enumDeclarationMetaModel = new EnumDeclarationMetaModel(this);

    public final ClassMetaModel explicitConstructorInvocationStmtMetaModel = new ExplicitConstructorInvocationStmtMetaModel(this);

    public final ClassMetaModel expressionMetaModel = new ExpressionMetaModel(this);

    public final ClassMetaModel expressionStmtMetaModel = new ExpressionStmtMetaModel(this);

    public final ClassMetaModel fieldAccessExprMetaModel = new FieldAccessExprMetaModel(this);

    public final ClassMetaModel fieldDeclarationMetaModel = new FieldDeclarationMetaModel(this);

    public final ClassMetaModel forStmtMetaModel = new ForStmtMetaModel(this);

    public final ClassMetaModel foreachStmtMetaModel = new ForeachStmtMetaModel(this);

    public final ClassMetaModel ifStmtMetaModel = new IfStmtMetaModel(this);

    public final ClassMetaModel importDeclarationMetaModel = new ImportDeclarationMetaModel(this);

    public final ClassMetaModel initializerDeclarationMetaModel = new InitializerDeclarationMetaModel(this);

    public final ClassMetaModel instanceOfExprMetaModel = new InstanceOfExprMetaModel(this);

    public final ClassMetaModel integerLiteralExprMetaModel = new IntegerLiteralExprMetaModel(this);

    public final ClassMetaModel intersectionTypeMetaModel = new IntersectionTypeMetaModel(this);

    public final ClassMetaModel javadocCommentMetaModel = new JavadocCommentMetaModel(this);

    public final ClassMetaModel labeledStmtMetaModel = new LabeledStmtMetaModel(this);

    public final ClassMetaModel lambdaExprMetaModel = new LambdaExprMetaModel(this);

    public final ClassMetaModel lineCommentMetaModel = new LineCommentMetaModel(this);

    public final ClassMetaModel literalExprMetaModel = new LiteralExprMetaModel(this);

    public final ClassMetaModel localClassDeclarationStmtMetaModel = new LocalClassDeclarationStmtMetaModel(this);

    public final ClassMetaModel longLiteralExprMetaModel = new LongLiteralExprMetaModel(this);

    public final ClassMetaModel markerAnnotationExprMetaModel = new MarkerAnnotationExprMetaModel(this);

    public final ClassMetaModel memberValuePairMetaModel = new MemberValuePairMetaModel(this);

    public final ClassMetaModel methodCallExprMetaModel = new MethodCallExprMetaModel(this);

    public final ClassMetaModel methodDeclarationMetaModel = new MethodDeclarationMetaModel(this);

    public final ClassMetaModel methodReferenceExprMetaModel = new MethodReferenceExprMetaModel(this);

    public final ClassMetaModel nameMetaModel = new NameMetaModel(this);

    public final ClassMetaModel nameExprMetaModel = new NameExprMetaModel(this);

    public final ClassMetaModel nodeMetaModel = new NodeMetaModel(this);

    public final ClassMetaModel nodeListMetaModel = new NodeListMetaModel(this);

    public final ClassMetaModel normalAnnotationExprMetaModel = new NormalAnnotationExprMetaModel(this);

    public final ClassMetaModel nullLiteralExprMetaModel = new NullLiteralExprMetaModel(this);

    public final ClassMetaModel objectCreationExprMetaModel = new ObjectCreationExprMetaModel(this);

    public final ClassMetaModel packageDeclarationMetaModel = new PackageDeclarationMetaModel(this);

    public final ClassMetaModel parameterMetaModel = new ParameterMetaModel(this);

    public final ClassMetaModel primitiveTypeMetaModel = new PrimitiveTypeMetaModel(this);

    public final ClassMetaModel referenceTypeMetaModel = new ReferenceTypeMetaModel(this);

    public final ClassMetaModel returnStmtMetaModel = new ReturnStmtMetaModel(this);

    public final ClassMetaModel simpleNameMetaModel = new SimpleNameMetaModel(this);

    public final ClassMetaModel singleMemberAnnotationExprMetaModel = new SingleMemberAnnotationExprMetaModel(this);

    public final ClassMetaModel statementMetaModel = new StatementMetaModel(this);

    public final ClassMetaModel stringLiteralExprMetaModel = new StringLiteralExprMetaModel(this);

    public final ClassMetaModel superExprMetaModel = new SuperExprMetaModel(this);

    public final ClassMetaModel switchEntryStmtMetaModel = new SwitchEntryStmtMetaModel(this);

    public final ClassMetaModel switchStmtMetaModel = new SwitchStmtMetaModel(this);

    public final ClassMetaModel synchronizedStmtMetaModel = new SynchronizedStmtMetaModel(this);

    public final ClassMetaModel thisExprMetaModel = new ThisExprMetaModel(this);

    public final ClassMetaModel throwStmtMetaModel = new ThrowStmtMetaModel(this);

    public final ClassMetaModel tryStmtMetaModel = new TryStmtMetaModel(this);

    public final ClassMetaModel typeMetaModel = new TypeMetaModel(this);

    public final ClassMetaModel typeDeclarationMetaModel = new TypeDeclarationMetaModel(this);

    public final ClassMetaModel typeExprMetaModel = new TypeExprMetaModel(this);

    public final ClassMetaModel typeParameterMetaModel = new TypeParameterMetaModel(this);

    public final ClassMetaModel unaryExprMetaModel = new UnaryExprMetaModel(this);

    public final ClassMetaModel unionTypeMetaModel = new UnionTypeMetaModel(this);

    public final ClassMetaModel unknownTypeMetaModel = new UnknownTypeMetaModel(this);

    public final ClassMetaModel variableDeclarationExprMetaModel = new VariableDeclarationExprMetaModel(this);

    public final ClassMetaModel variableDeclaratorMetaModel = new VariableDeclaratorMetaModel(this);

    public final ClassMetaModel voidTypeMetaModel = new VoidTypeMetaModel(this);

    public final ClassMetaModel whileStmtMetaModel = new WhileStmtMetaModel(this);

    public final ClassMetaModel wildcardTypeMetaModel = new WildcardTypeMetaModel(this);
}

