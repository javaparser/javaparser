package me.tomassetti.symbolsolver.model;

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
        return JavaParser.parse(is);
    }
}
