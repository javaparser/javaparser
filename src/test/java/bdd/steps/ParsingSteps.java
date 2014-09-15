package bdd.steps;

import japa.parser.JavaParser;
import japa.parser.ParseException;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.ClassOrInterfaceDeclaration;
import japa.parser.ast.body.ConstructorDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import org.jbehave.core.annotations.Given;
import org.jbehave.core.annotations.Then;
import org.jbehave.core.annotations.When;

import java.io.ByteArrayInputStream;

import static org.hamcrest.core.Is.is;
import static org.junit.Assert.assertThat;

public class ParsingSteps {

    private CompilationUnit compilationUnit;

    @Given("a CompilationUnit")
    public void givenACompilationUnit() {
        compilationUnit = new CompilationUnit();
    }

    @When("the following source is parsed:$classSrc")
    public void whenTheFollowingSourceIsParsed(String classSrc) throws ParseException {
        compilationUnit = JavaParser.parse(new ByteArrayInputStream(classSrc.getBytes()));
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

}
