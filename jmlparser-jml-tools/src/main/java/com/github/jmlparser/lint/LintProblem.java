package com.github.jmlparser.lint;

import com.github.javaparser.TokenRange;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public record LintProblem(
        @NotNull
        String level,
        @NotNull
        String message,
        @Nullable
        TokenRange location,
        @Nullable
        Throwable cause,
        @Nullable
        String category,
        @NotNull
        String ruleId) {

    public LintProblem(@NotNull String level, @NotNull String message, @Nullable TokenRange location, @NotNull String ruleId) {
        this(level, message, location, null, null, ruleId);
    }
}
