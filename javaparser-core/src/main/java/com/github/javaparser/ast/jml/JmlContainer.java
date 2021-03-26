package com.github.javaparser.ast.jml;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.JavaToken;
import com.github.javaparser.Range;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */
public interface JmlContainer<R extends Node, T extends Node> extends Jmlish {
    NodeList<T> getElements();

    R setElements(NodeList<T> elements);

    NodeList<SimpleName> getJmlTags();

    R setJmlTags(NodeList<SimpleName> jmlTags);

    boolean isSingleLine();

    R setSingleLine(boolean singleLine);

    default void setTagsFromStart(JavaToken token) {
        if (token.getText().trim().length() <= 3) return;
        String tags = token.getText().trim().substring(2);
        Range range = token.getRange().get();
        tags = tags.substring(0, tags.length() - 1);
        NodeList<SimpleName> name = new NodeList<>();
        int start = 2 + range.begin.column;

        String[] split = tags.split("(?=[+-])");
        for (String tag : split) {
            JavaToken t = new JavaToken(GeneratedJavaParserConstants.IDENTIFIER, tag);
            t.setRange(range.withBeginColumn(start).withEndColumn(start + tag.length()));
            SimpleName lbl = new SimpleName(new TokenRange(t, t), tag);
            name.add(lbl);
            start += tag.length() + 1;
        }
        setJmlTags(name);
    }
}
