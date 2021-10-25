package com.github.javaparser.ast.jml;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/21)
 */
public class JmlImportDeclaration extends ImportDeclaration implements Jmlish, HasJmlTags<JmlImportDeclaration> {
    private NodeList<SimpleName> jmlTags = new NodeList<>();

    public JmlImportDeclaration(String name, boolean isStatic, boolean isAsterisk) {
        super(name, isStatic, isAsterisk);
    }

    public JmlImportDeclaration(Name name, boolean isStatic, boolean isAsterisk, NodeList<SimpleName> jmltags) {
        super(name, isStatic, isAsterisk);
        this.jmlTags = jmltags;
    }

    public JmlImportDeclaration(TokenRange tokenRange, Name name, boolean isStatic, boolean isAsterisk) {
        super(tokenRange, name, isStatic, isAsterisk);
    }

    public JmlImportDeclaration(TokenRange range, ImportDeclaration in, DefaultJmlContainer c) {
        super(range, in.getName(), in.isStatic(), in.isAsterisk());
        jmlTags = c.getJmlTags();
    }

    @Override
    public JmlImportDeclaration setJmlTags(NodeList<SimpleName> jmlTags) {
        return null;
    }

    @Override
    public NodeList<SimpleName> getJmlTags() {
        return null;
    }
}
