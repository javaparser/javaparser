package japa.parser.comments;

public class ClassWithLineCommentInsideBlockComment {

    /* comment to a method */
    void foo(){}

    /*// Line Comment put immediately after block comment

    //// Comment debauchery

    another orphan.
    It spans over more lines */
}