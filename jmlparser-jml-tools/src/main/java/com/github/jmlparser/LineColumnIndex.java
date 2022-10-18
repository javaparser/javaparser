package com.github.jmlparser;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import org.jetbrains.annotations.NotNull;

/**
 * The index is 1-based. The first character also begins in line 1 and column 1.
 *
 * @author Alexander Weigl
 * @version 1 (18.10.22)
 */
public class LineColumnIndex {
    private final String content;
    int[] lineOffsets;

    public LineColumnIndex(@NotNull String content) {
        this.content = content;
        lineOffsets = new int[1 + (int) content.chars().filter(it -> it == '\n').count()];
        int cur = 1;
        final var chars = content.toCharArray();
        for (int i = 0; i < chars.length; i++) {
            if (chars[i] == '\n')
                lineOffsets[cur++] = i + 1;
        }
    }

    public String substring(Range range) {
        return substring(range.begin, range.end);
    }

    private String substring(Position begin, Position end) {
        return substring(begin.line, begin.column, end.line, end.column);
    }

    public String substring(int beginLine, int beginColumn, int endLine, int endColumn) {
        var a = positionToOffset(beginLine, beginColumn);
        var b = positionToOffset(endLine, endColumn);
        return content.substring(a, b + 1);
    }

    public int positionToOffset(Position p) {
        return positionToOffset(p.line, p.column);
    }

    public int positionToOffset(int line, int column) {
        return lineOffsets[line - 1] + column - 1;
    }
}
