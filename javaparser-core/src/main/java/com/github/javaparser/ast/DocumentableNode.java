package com.github.javaparser.ast;

import com.github.javaparser.ast.comments.JavadocComment;

/**
 * Node which can be documented through a Javadoc comment.
 */
public interface DocumentableNode {

    public JavadocComment getJavaDoc();
    public void setJavaDoc(JavadocComment javadocComment);
}
