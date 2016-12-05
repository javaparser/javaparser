package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.StreamProvider;
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
    public void packageProtectedMethodShouldHavePositionSet() throws IOException {
      ensureAllNodesHaveValidBeginPosition("SourcesHelperOldVersion.java.txt");
    }

    @Test
    public void packageProtectedConstructorShouldHavePositionSet() throws IOException {
      ensureAllNodesHaveValidBeginPosition("PackageProtectedCtorNodePositionTest.java.txt");
    }

    private void ensureAllNodesHaveValidBeginPosition(final String testResourceName) throws IOException {
        InputStream is = this.getClass().getResourceAsStream("/com/github/javaparser/issue_samples/" + testResourceName);
        ParseResult<CompilationUnit> res = new JavaParser().parse(ParseStart.COMPILATION_UNIT, new StreamProvider(is));
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
