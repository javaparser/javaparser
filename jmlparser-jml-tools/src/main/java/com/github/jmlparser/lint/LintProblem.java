package com.github.jmlparser.lint;

import com.github.javaparser.TokenRange;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public final class LintProblem {
    @NotNull
    private final String level;
    @NotNull
    private final String message;
    @Nullable
    private final TokenRange location;
    @Nullable
    private final Throwable cause;
    @Nullable
    private final String category;

    public LintProblem(@NotNull String level, @NotNull String message, @Nullable TokenRange location) {
        this(level, message, location, null, null);
    }

    public LintProblem(@NotNull String level, @NotNull String message,
                       @Nullable TokenRange location, @Nullable Throwable cause, @Nullable String category) {
        this.level = level;
        this.message = message;
        this.location = location;
        this.cause = cause;
        this.category = category;
    }


    @NotNull
    public String message() {
        return message;
    }

    @Nullable
    public TokenRange location() {
        return location;
    }

    @Nullable
    public Throwable cause() {
        return cause;
    }

    @NotNull
    public String level() {
        return level;
    }

    @Nullable
    public String category() {
        return category;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (obj == null || obj.getClass() != this.getClass()) return false;
        var that = (LintProblem) obj;
        return Objects.equals(this.message, that.message) &&
                Objects.equals(this.location, that.location) &&
                Objects.equals(this.cause, that.cause) &&
                Objects.equals(this.level, that.level) &&
                Objects.equals(this.category, that.category);
    }

    @Override
    public int hashCode() {
        return Objects.hash(message, location, cause, level, category);
    }

    @Override
    public String toString() {
        return "LintProblem[" +
                "message=" + message + ", " +
                "location=" + location + ", " +
                "cause=" + cause + ", " +
                "level=" + level + ", " +
                "category=" + category + ']';
    }
}
