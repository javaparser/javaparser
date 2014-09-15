package bdd.steps;

import japa.parser.JavaParser;
import japa.parser.ParseException;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.*;
import japa.parser.ast.expr.AnnotationExpr;
import japa.parser.ast.visitor.CloneVisitor;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.ByteArrayInputStream;

import static bdd.steps.CommonSteps.getMemberByTypeAndPosition;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsEqual.equalTo;
import static org.hamcrest.core.IsNot.not;
import static org.junit.Assert.assertThat;

public class ParsingSteps {

    private CompilationUnit compilationUnit;

    private CompilationUnit secondCompilationUnit;

    @Given("a CompilationUnit")
    public void givenACompilationUnit() {
        compilationUnit = new CompilationUnit();
    }

    @Given("a second CompilationUnit")
    public void givenASecondCompilationUnit() {
        secondCompilationUnit = new CompilationUnit();
    }

    @When("the following source is parsed:$classSrc")
    public void whenTheFollowingSourceIsParsed(String classSrc) throws ParseException {
        compilationUnit = JavaParser.parse(new ByteArrayInputStream(classSrc.getBytes()));
    }

    @When("the following sources is parsed by the second CompilationUnit:$classSrc")
    public void whenTheFollowingSourcesIsParsedBytTheSecondCompilationUnit(String classSrc) throws ParseException {
        secondCompilationUnit = JavaParser.parse(new ByteArrayInputStream(classSrc.getBytes()));
    }

    @When("the CompilationUnit is cloned to the second CompilationUnit")
    public void whenTheSecondCompilationUnitIsCloned() {
        secondCompilationUnit = (CompilationUnit)compilationUnit.accept(new CloneVisitor(), null);
    }

    @Then("constructor $constructorPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenTheConstructorDeclarationAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(), is(expectedString));
    }

    @Then("constructor $constructorPosition in class $classPosition declaration short form as a String is \"$expectedString\"")
    public void thenConstructorInClassDeclarationShortFormAsAStringIs(int constructorPosition, int classPosition, String expectedString) {
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition - 1);
        ConstructorDeclaration constructor = (ConstructorDeclaration)clazz.getMembers().get(constructorPosition - 1);
        assertThat(constructor.getDeclarationAsString(false,false), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String is \"$expectedString\"")
    public void thenMethod1InClass1DeclarationAsAStringIs(int methodPosition, int classPosition, String expectedString) {
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition -1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(), is(expectedString));
    }

    @Then("method $methodPosition in class $classPosition declaration as a String short form is \"$expectedString\"")
    public void thenMethodInClassDeclarationAsAStringShortFormIs(int methodPosition, int classPosition, String expectedString) {
        ClassOrInterfaceDeclaration clazz = (ClassOrInterfaceDeclaration)compilationUnit.getTypes().get(classPosition -1);
        MethodDeclaration method = (MethodDeclaration)clazz.getMembers().get(methodPosition -1);
        assertThat(method.getDeclarationAsString(false, false), is(expectedString));
    }

    @Then("the CompilationUnit is equal to the second CompilationUnit")
    public void thenTheCompilationUnitIsEqualToTheSecondCompilationUnit() {
        assertThat(compilationUnit, is(equalTo(secondCompilationUnit)));
    }

    @Then("the CompilationUnit has the same hashcode to the second CompilationUnit")
    public void thenTheCompilationUnitHasTheSameHashcodeToTheSecondCompilationUnit() {
        assertThat(compilationUnit.hashCode(), is(equalTo(secondCompilationUnit.hashCode())));
    }

    @Then("the CompilationUnit is not equal to the second CompilationUnit")
    public void thenTheCompilationUnitIsNotEqualToTheSecondCompilationUnit() {
        assertThat(compilationUnit, not(equalTo(secondCompilationUnit)));
    }

    @Then("the CompilationUnit has a different hashcode to the second CompilationUnit")
    public void thenTheCompilationUnitHasADifferentHashcodeToTheSecondCompilationUnit() {
        assertThat(compilationUnit.hashCode(), not(equalTo(secondCompilationUnit.hashCode())));
    }

    @Then("field $fieldPosition in class $classPosition contains annotation $annotationPosition value is \"$expectedValue\"")
    public void thenFieldInClassContainsAnnotationValueIs(int fieldPosition, int classPosition, int annotationPosition, String expectedValue) {
        TypeDeclaration classUnderTest = compilationUnit.getTypes().get(classPosition - 1);
        FieldDeclaration fieldUnderTest = (FieldDeclaration) getMemberByTypeAndPosition(classUnderTest, fieldPosition - 1,
                FieldDeclaration.class);
        AnnotationExpr annotationUnderTest = fieldUnderTest.getAnnotations().get(annotationPosition - 1);
        assertThat(annotationUnderTest.getChildrenNodes().get(1).toString(), is(expectedValue));
    }


}
