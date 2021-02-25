package com.github.javaparser.jml.impl;

import com.github.javaparser.jml.services.IJmlTagger;
import jml.JmlComment;
import org.jetbrains.annotations.NotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/3/20)
 */
public class JmlTagger implements IJmlTagger {
    @Override
    public void modifyTags(@NotNull JmlComment comment) {
        //does nothing
    }
}
