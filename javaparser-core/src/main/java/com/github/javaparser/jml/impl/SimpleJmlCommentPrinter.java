package jml.impl;

import jml.JmlComment;
import jml.services.IJmlCommentPrinter;
import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (4/5/20)
 */
public class SimpleJmlCommentPrinter implements IJmlCommentPrinter {
    @Override
    public void print(@NotNull StringBuffer buf, @NotNull JmlComment comment, @NotNull String indent, boolean debug) {
        if (comment != null) {
            printWithNewIndent(comment.getContent(), buf, indent);
            if (debug) {
                buf.append("\n").append(indent);
                buf.append("/*").append(comment.getAnnotations()).append("*/");
                buf.append("\n").append(indent);
                //buf.append("/*").append(comment.getContext().getText()).append("*/");
                buf.append("\n").append(indent);
                buf.append("/*").append(comment.getParserErrors()).append("*/");
            }
        }
    }

    private void printWithNewIndent(String content, StringBuffer buf, String indent) {
        String nc = content.replaceAll("\n[\t ]*", indent+"  @ ");
        buf.append(indent).append(nc);
    }
}
