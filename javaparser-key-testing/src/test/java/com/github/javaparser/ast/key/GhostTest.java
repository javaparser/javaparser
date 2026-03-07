package com.github.javaparser.ast.key;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.body.MethodDeclaration;
import java.io.IOException;
import java.nio.file.Paths;
import org.junit.jupiter.api.Test;

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/4/26)
 */
public class GhostTest {

    @Test
    void m() throws IOException {
        final var configuration = new ParserConfiguration();
        configuration.setLanguageLevel(ParserConfiguration.LanguageLevel.RAW);
        var parser = new JavaParser(configuration);
        var cu = parser.parse(Paths.get("src/test/resources/Ghost.java"));
        final var result = cu.getResult().get();
        var body = ((MethodDeclaration) result.getPrimaryType().get().members().get(1))
                .getBody()
                .get();
        System.out.println(result);
    }
}
