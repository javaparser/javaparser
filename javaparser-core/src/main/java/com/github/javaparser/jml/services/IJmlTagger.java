package com.github.javaparser.jml.services;

import jml.JmlAnnotations;
import jml.JmlComment;
import org.jetbrains.annotations.NotNull;

/**
 * This services is responsible for re-tagging of Jml comments.
 * <p>
 * Re-tagging means, that after a JmlAst is created, you can decide whether the corresponding
 * Jml comment should receive different {@link JmlAnnotations}s.
 *
 * <p>
 * For example you want to tag, that certain operators are not suitable for KeY, then you should detect these in
 * <code>ctx</code> and call <code>target.disable("KeY")</code>
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (2/2/20)
 */
public interface IJmlTagger {
    void modifyTags(@NotNull JmlComment comment);
}
