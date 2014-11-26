package japa.parser.ast;

import japa.parser.ast.comments.JavadocComment;

/**
 * Created with IntelliJ IDEA.
 * User: federico
 * Date: 10/24/13
 * Time: 3:24 PM
 * To change this template use File | Settings | File Templates.
 */
public interface DocumentableNode {

    public JavadocComment getJavaDoc();
    public void setJavaDoc(JavadocComment javadocComment);
}
