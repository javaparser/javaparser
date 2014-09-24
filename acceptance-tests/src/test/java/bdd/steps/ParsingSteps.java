package bdd.steps;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.*;
import japa.parser.ast.expr.AnnotationExpr;
import org.jbehave.core.annotations.Then;

import java.util.Map;

import static bdd.steps.SharedSteps.getMemberByTypeAndPosition;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNot.not;
import static org.junit.Assert.assertThat;

public class ParsingSteps {

    private Map<String, Object> state;

    public ParsingSteps(Map<String, Object> state){
        this.state = state;
    }

    @Then("constructor $constructorPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenTheConstructorDeclarationAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(), is(expectedString));
    }

    @Then("constructor $constructorPosition in class $classPosition declaration short form as a String is \"$expectedString\"")
    public void thenConstructorInClassDeclarationShortFormAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(false,false), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenMethod1InClass1DeclarationAsAStringIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition -1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String short form is \"$expectedString\"")
    public void thenMethodInClassDeclarationAsAStringShortFormIs(int methodPosition, int classPosition, String expectedString) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition -1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(false, false), is(expectedString));
    }

    @Then("field $fieldPosition in class $classPosition contains annotation $annotationPosition value is \"$expectedValue\"")
    public void thenFieldInClassContainsAnnotationValueIs(int fieldPosition, int classPosition, int annotationPosition, String expectedValue) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");

        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        AnnotationExpr annotationUnderTest = fieldUnderTest.getAnnotations().get(annotationPosition - 1);
        assertThat(annotationUnderTest.getChildrenNodes().get(1).toString(), is(expectedValue));
    }

    @Then("lambda $lambdaPosition in class $classPosition is refereced \"$expectedValue\"")
    public void thenLambdaInClassIsCalled(int lambdaPosition, int classPosition, String expectedValue) {
        CompilationUnit compilationUnit = (CompilationUnit) state.get("cu1");
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
    }
}
