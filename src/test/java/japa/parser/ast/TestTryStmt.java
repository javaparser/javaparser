package japa.parser.ast;

import japa.parser.ast.body.VariableDeclarator;
import japa.parser.ast.body.VariableDeclaratorId;
import japa.parser.ast.expr.VariableDeclarationExpr;
import japa.parser.ast.stmt.TryStmt;
import japa.parser.ast.type.ClassOrInterfaceType;
import org.junit.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.theInstance;

import java.util.List;

import static java.util.Arrays.asList;


public final class TestTryStmt {

    @Test
    public void setsItselfAsParentForResources() {
        ClassOrInterfaceType closeableType = new ClassOrInterfaceType(new ClassOrInterfaceType(new ClassOrInterfaceType("java"), "io"), "Closeable");
        List<VariableDeclarator> variableDeclarators = asList(new VariableDeclarator(new VariableDeclaratorId("closeable")));
        List<VariableDeclarationExpr> variableDeclarationExprs = asList(new VariableDeclarationExpr(closeableType, variableDeclarators));

        TryStmt objectUnderTest = new TryStmt();
        objectUnderTest.setResources(variableDeclarationExprs);

        Node expectedParent = objectUnderTest;
        for (VariableDeclarationExpr variableDeclarationExpr : variableDeclarationExprs) {
            assertThat(variableDeclarationExpr.getParentNode(), is(theInstance(expectedParent)));
        }
    }

    @Test
    public void handlesNullResourcesGracefully() {
        TryStmt objectUnderTest = new TryStmt();
        objectUnderTest.setResources(null);

        assertThat(objectUnderTest.getChildrenNodes().isEmpty(), is(true));
    }

}
