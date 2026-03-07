package com.github.javaparser.ast.key;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (3/3/26)
 */
public class JmlDocModifier implements Modifier.Keyword {

    private NodeList<JmlDoc> jmlDocs;

    @AllFieldsConstructor
    public JmlDocModifier(NodeList<JmlDoc> jmlDocs) {
        this.jmlDocs = jmlDocs;
    }

    @Override
    public String name() {
        return asString();
    }

    @Override
    public String asString() {
        return jmlDocs.stream().map(it -> it.getContent().asString()).collect(Collectors.joining(" "));
    }

    public NodeList<JmlDoc> getJmlDocs() {
        return jmlDocs;
    }

    public void setJmlDocs(NodeList<JmlDoc> jmlDocs) {
        this.jmlDocs = jmlDocs;
    }
}
