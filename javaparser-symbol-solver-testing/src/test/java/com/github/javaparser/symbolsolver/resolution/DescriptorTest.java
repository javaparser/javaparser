package com.github.javaparser.symbolsolver.resolution;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import com.github.javaparser.ast.body.ConstructorDeclaration;
import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class DescriptorTest extends AbstractResolutionTest {

    @Test
    void descriptorTest() {
        String code = 
                "public class A {\n" +
                "  A(int i, double d, Thread t) {}\n" +
                "  Object m(int i, double d, Thread t) {return new Object();}\n" +
                "  void m(int i, double d, Thread t) {}\n" +
                "  int[] m(int i, double d, Thread t) {return new int[] {};}\n" +
                "  long[][] m(int i, double d, Thread t) {return new long[][] {};}\n" +
                "  void m() {}\n" +
                "}";
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parse(code);

        List<ConstructorDeclaration> constructor = cu.findAll(ConstructorDeclaration.class);
        assertEquals("(IDLjava/lang/Thread;)V", constructor.get(0).toDescriptor());

        List<MethodDeclaration> methods = cu.findAll(MethodDeclaration.class);
        // exemple provided in https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.3
        assertEquals("(IDLjava/lang/Thread;)Ljava/lang/Object;", methods.get(0).toDescriptor());
        // with void return type
        assertEquals("(IDLjava/lang/Thread;)V", methods.get(1).toDescriptor());
        // with single array type
        assertEquals("(IDLjava/lang/Thread;)[I", methods.get(2).toDescriptor());
        // with single array type
        assertEquals("(IDLjava/lang/Thread;)[[J", methods.get(3).toDescriptor());
       // with void return type and no parameter
        assertEquals("()V", methods.get(4).toDescriptor());
    }
}
