package me.tomassetti.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;

import java.io.InputStream;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractTest {

    protected CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = this.getClass().getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        CompilationUnit cu = JavaParser.parse(is);
        if (cu == null) {
            throw new IllegalStateException();
        }
        return cu;
    }
}
