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

public class NodePositionTest {

    private List<Node> getAllNodes(Node node) {
        List<Node> nodes = new LinkedList<>();
        nodes.add(node);
        node.getChildrenNodes().forEach(c -> nodes.addAll(getAllNodes(c)));
        return nodes;
    }

    @Test
    public void issue506() throws IOException {
        InputStream is = this.getClass().getResourceAsStream("/com/github/javaparser/SourcesHelperOldVersion.java.txt");
        ParseResult<CompilationUnit> res = new JavaParser().parse(ParseStart.COMPILATION_UNIT, new StreamProvider(is));

        CompilationUnit cu = res.getResult().get();
        getAllNodes(cu).forEach(n -> {
            if (n.getBegin().line == 0) {
                throw new IllegalArgumentException("There should be no node at line 0");
            }
        });
    }
}
