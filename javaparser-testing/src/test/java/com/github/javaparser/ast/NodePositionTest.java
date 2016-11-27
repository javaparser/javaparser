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

import static org.junit.Assert.assertTrue;

public class NodePositionTest {

    private List<Node> getAllNodes(Node node) {
        List<Node> nodes = new LinkedList<>();
        nodes.add(node);
        node.getChildNodes().forEach(c -> nodes.addAll(getAllNodes(c)));
        return nodes;
    }

    @Test
    public void issue506() throws IOException {
        InputStream is = this.getClass().getResourceAsStream("/com/github/javaparser/SourcesHelperOldVersion.java.txt");
        ParseResult<CompilationUnit> res = new JavaParser().parse(ParseStart.COMPILATION_UNIT, new StreamProvider(is));
        assertTrue(res.getProblems().isEmpty());

        CompilationUnit cu = res.getResult().get();
        getAllNodes(cu).forEach(n -> {
            if (n.getRange() == null) {
                throw new IllegalArgumentException("There should be no node without a range: " + n + " (class: "
                        + n.getClass().getCanonicalName() + ")");
            }
            if (n.getBegin().get().line == 0 && !n.toString().isEmpty() && !(n instanceof ArrayBracketPair)) {
                throw new IllegalArgumentException("There should be no node at line 0: " + n + " (class: "
                        + n.getClass().getCanonicalName() + ")");
            }
        });
    }
}
