package com.github.javaparser.key;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (29.06.23)
 */
public class KeYParsingTests {
    @Test
    void testGhostModifier() {
        Statement x = StaticJavaParser.parseStatement("ghost int x;");
    }

    @Test
    void testDLEscape() {
        Statement x = StaticJavaParser.parseStatement("x = \\dl_union(y,z);");
    }
}
