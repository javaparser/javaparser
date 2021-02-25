package com.github.javaparser.jml.services;

import jml.JmlComment;
import org.jetbrains.annotations.NotNull;

/**
 * Interface describe a Service for printing {@link JmlComment}.
 *
 * @author Alexander Weigl
 * @version 1 s(4/5/20)
 */
public interface IJmlCommentPrinter {
    /**
     * This method should print the given {@code comment} into the {@code buf}.
     *
     * @param buf     a sink for printing
     * @param comment the comment to be printed
     * @param indent  current indentation level
     * @param debug   if true, print debugging information
     */
    void print(@NotNull StringBuffer buf,
               @NotNull JmlComment comment,
               @NotNull String indent,
               boolean debug);
}
