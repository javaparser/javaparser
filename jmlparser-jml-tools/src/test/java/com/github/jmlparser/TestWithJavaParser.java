package com.github.jmlparser;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class TestWithJavaParser {
    protected final JavaParser parser;
    protected final Node parent;

    {
        ParserConfiguration config = new ParserConfiguration();
        config.setProcessJml(true);
        config.setSymbolResolver(new JavaSymbolSolver(new ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader())));
        parser = new JavaParser(config);

        final var resourceAsStream = getClass().getResourceAsStream("Test.java");
        if (resourceAsStream != null) {
            ParseResult<CompilationUnit> r = parser.parse(resourceAsStream);
            if (!r.isSuccessful()) {
                r.getProblems().forEach(System.err::println);
                fail("Error during parsing");
            }
            parent = r.getResult().get().getType(0);
        } else {
            parent = null;
        }
    }
}
