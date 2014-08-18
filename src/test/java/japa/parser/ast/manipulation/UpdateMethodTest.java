package japa.parser.ast.manipulation;

import fixture.Helper;
import japa.parser.ASTHelper;
import japa.parser.JavaParser;
import japa.parser.ast.CompilationUnit;
import japa.parser.ast.body.BodyDeclaration;
import japa.parser.ast.body.MethodDeclaration;
import japa.parser.ast.body.Parameter;
import japa.parser.ast.body.TypeDeclaration;
import japa.parser.ast.visitor.VoidVisitorAdapter;
import org.junit.Test;

import java.io.FileInputStream;
import java.util.List;

import static org.hamcrest.CoreMatchers.containsString;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.MatcherAssert.assertThat;


public class UpdateMethodTest {

    private static final String METHOD_ONE_NAME = "changeToUpperCase";
    private static final String METHOD_TWO_NAME = "anotherMethodToChange";

    private static final Parameter INT_VALUE_ARG = ASTHelper.createParameter(ASTHelper.INT_TYPE, "value");

    @Test
    public void shouldChangeMethodNamesToUpperCase() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("UpdateMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        List<TypeDeclaration> types = cu.getTypes();
        for (TypeDeclaration type : types) {
            List<BodyDeclaration> members = type.getMembers();
            for (BodyDeclaration member : members) {
                if (member instanceof MethodDeclaration) {
                    MethodDeclaration method = (MethodDeclaration) member;
                    method.setName(method.getName().toUpperCase());
                }
            }
        }

        String sourceUnderTest = cu.toString();

        assertThat(sourceUnderTest, containsString(METHOD_ONE_NAME.toUpperCase()));
        assertThat(sourceUnderTest, containsString(METHOD_TWO_NAME.toUpperCase()));
    }

    @Test
    public void shouldAddNewParameterToMethod() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("UpdateMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        List<TypeDeclaration> types = cu.getTypes();
        for (TypeDeclaration type : types) {
            List<BodyDeclaration> members = type.getMembers();
            for (BodyDeclaration member : members) {
                if (member instanceof MethodDeclaration) {
                    MethodDeclaration method = (MethodDeclaration) member;
                    ASTHelper.addParameter(method, INT_VALUE_ARG);
                }
            }
        }

        MethodDeclaration methodOne = (MethodDeclaration)cu.getChildrenNodes().get(1).getChildrenNodes().get(0);
        MethodDeclaration methodTwo = (MethodDeclaration)cu.getChildrenNodes().get(1).getChildrenNodes().get(1);

        Parameter methodOneParameter = methodOne.getParameters().get(0);
        Parameter methodTwoParameter = methodTwo.getParameters().get(0);

        assertThat(methodOneParameter, is(INT_VALUE_ARG));
        assertThat(methodTwoParameter, is(INT_VALUE_ARG));
    }

    @Test
    public void shouldChangeMethodNamesToUpperCaseUsingVisitor() throws Exception {

        String source = Helper.readStream(getClass().getResourceAsStream("UpdateMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        new ChangeMethodNameToUpperCaseVisitor().visit(cu, null);

        String sourceUnderTest = cu.toString();

        assertThat(sourceUnderTest, containsString(METHOD_ONE_NAME.toUpperCase()));
        assertThat(sourceUnderTest, containsString(METHOD_TWO_NAME.toUpperCase()));
    }

    @Test
    public void shouldAddNewParameterToMethodUsingVisitor() throws Exception {

        String source = Helper.readStream(getClass().getResourceAsStream("UpdateMethod.java"));
        CompilationUnit cu = Helper.parserString(source);

        new AddNewParameterCalledValueVisitor().visit(cu, null);

        MethodDeclaration methodOne = (MethodDeclaration)cu.getChildrenNodes().get(1).getChildrenNodes().get(0);
        MethodDeclaration methodTwo = (MethodDeclaration)cu.getChildrenNodes().get(1).getChildrenNodes().get(1);

        Parameter methodOneParameter = methodOne.getParameters().get(0);
        Parameter methodTwoParameter = methodTwo.getParameters().get(0);

        assertThat(methodOneParameter, is(INT_VALUE_ARG));
        assertThat(methodTwoParameter, is(INT_VALUE_ARG));
    }

    private static class ChangeMethodNameToUpperCaseVisitor extends VoidVisitorAdapter<Void> {

        @Override
        public void visit(MethodDeclaration n, Void arg) {
            n.setName(n.getName().toUpperCase());
        }
    }

    private static class AddNewParameterCalledValueVisitor extends VoidVisitorAdapter<Void> {

        @Override
        public void visit(MethodDeclaration n, Void arg) {
            ASTHelper.addParameter(n, INT_VALUE_ARG);
        }
    }
}