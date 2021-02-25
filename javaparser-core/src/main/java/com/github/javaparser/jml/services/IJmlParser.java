package com.github.javaparser.jml.services;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.comments.Comment;
import jml.JmlComment;
import jml.JmlSpecs;
import org.jetbrains.annotations.NotNull;

import java.util.List;

/**
 * This Service provides functionality of translating
 * the String content of a {@link JmlComment} into a parse tree.
 *
 * @author Alexander Weigl
 * @version 1 (1/30/20)
 * @see JmlComment#getContext()
 * @see ParserRuleContext
 */
public interface IJmlParser {
    /**
     * Parses the String content into a parse tree.
     * <p>
     * The parse tree is after execution set {@link JmlComment#setContext}.
     * Problems found during parsing should be reported to {@link JmlComment#getParserErrors()}
     *
     * @param comment a jml comment
     */
    List<Jmlish> create(@NotNull Comment comment);
}
