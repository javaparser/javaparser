package com.github.javaparser.ast;

import com.github.javaparser.*;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class NodePositionTest {

    private List<Node> getAllNodes(Node node) {
        List<Node> nodes = new LinkedList<>();
        nodes.add(node);
        node.getChildNodes().forEach(c -> nodes.addAll(getAllNodes(c)));
        return nodes;
    }

    @Test
    public void packageProtectedClassShouldHavePositionSet() throws IOException {
        ensureAllNodesHaveValidBeginPosition("class A { }");
    }

    @Test
    public void packageProtectedInterfaceShouldHavePositionSet() throws IOException {
        ensureAllNodesHaveValidBeginPosition("interface A { }");
    }

    @Test
    public void packageProtectedEnumShouldHavePositionSet() throws IOException {
        ensureAllNodesHaveValidBeginPosition("enum A { }");
    }

    @Test
    public void packageProtectedAnnotationShouldHavePositionSet() throws IOException {
        ensureAllNodesHaveValidBeginPosition("@interface A { }");
    }

    @Test
    public void packageProtectedFieldShouldHavePositionSet() throws IOException {
        ensureAllNodesHaveValidBeginPosition("public class A { int i; }");
    }

    @Test
    public void packageProtectedMethodShouldHavePositionSet() throws IOException {
      ensureAllNodesHaveValidBeginPosition("public class A { void foo() {} }");
    }

    @Test
    public void packageProtectedConstructorShouldHavePositionSet() throws IOException {
      ensureAllNodesHaveValidBeginPosition("public class A { A() {} }");
    }

    private void ensureAllNodesHaveValidBeginPosition(final String code) throws IOException {
        ParseResult<CompilationUnit> res = new JavaParser().parse(ParseStart.COMPILATION_UNIT, Providers.provider(code));
        assertTrue(res.getProblems().isEmpty());

        CompilationUnit cu = res.getResult().get();
        getAllNodes(cu).forEach(n -> {
            assertNotNull(String.format("There should be no node without a range: %s (class: %s)",
                    n, n.getClass().getCanonicalName()), n.getRange());
            if (n.getBegin().get().line == 0 && !n.toString().isEmpty() && !(n instanceof ArrayBracketPair)) {
                throw new IllegalArgumentException("There should be no node at line 0: " + n + " (class: "
                        + n.getClass().getCanonicalName() + ")");
            }
        });
    }
}
