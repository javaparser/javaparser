package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class DescriptorTest extends AbstractResolutionTest {

    @Test
    void descriptorTest() throws IOException {
        String code =
                "import javassist.ClassPool;\n" +
                "public class A {\n" +
                "  A(int i, double d, Thread t) {}\n" +
                "  public enum TestEnum {\n" +
                "    TEST_ENUM(\"test\");" +
                "    private String a;\n" +
                "    private TestEnum(String a) {\n" +
                "      this.a = a;\n" +
                "    }\n" +
                "  }\n" +
                "  Object m(int i, double d, Thread t) {return new Object();}\n" +
                "  void m(int i, double d, Thread t) {}\n" +
                "  int[] m(int i, double d, Thread t) {return new int[] {};}\n" +
                "  long[][] m(int i, double d, Thread t) {return new long[][] {};}\n" +
                "  void m() {\n" +
                "    System.out.println(\"a\");\n" +
                "    ClassPool cp = ClassPool.getDefault();\n" +
                "    TestEnum.valueOf(\"TEST_ENUM\");\n" +
                "    TestEnum.values();\n" +
                "  }\n" +
                "}";

        Path javassistJar = adaptPath("src/test/resources/issue3808/javassist-3.29.2-GA.jar");
        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(
                new CombinedTypeSolver(new ReflectionTypeSolver(),
                        new JarTypeSolver(javassistJar))));
        StaticJavaParser.setConfiguration(config);
        CompilationUnit cu = parse(code);

        List<ConstructorDeclaration> constructor = cu.findAll(ConstructorDeclaration.class);
        assertEquals("(IDLjava/lang/Thread;)V", constructor.get(0).toDescriptor());

        List<MethodDeclaration> methods = cu.findAll(MethodDeclaration.class);
        // exemple provided in https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.3
        assertEquals("(IDLjava/lang/Thread;)Ljava/lang/Object;", methods.get(0).toDescriptor());
        assertEquals("(IDLjava/lang/Thread;)Ljava/lang/Object;", methods.get(0).resolve().toDescriptor());
        // with void return type
        assertEquals("(IDLjava/lang/Thread;)V", methods.get(1).toDescriptor());
        assertEquals("(IDLjava/lang/Thread;)V", methods.get(1).resolve().toDescriptor());
        // with single array type
        assertEquals("(IDLjava/lang/Thread;)[I", methods.get(2).toDescriptor());
        assertEquals("(IDLjava/lang/Thread;)[I", methods.get(2).resolve().toDescriptor());
        // with single array type
        assertEquals("(IDLjava/lang/Thread;)[[J", methods.get(3).toDescriptor());
        assertEquals("(IDLjava/lang/Thread;)[[J", methods.get(3).resolve().toDescriptor());
        // with void return type and no parameter
        assertEquals("()V", methods.get(4).toDescriptor());
        assertEquals("()V", methods.get(4).resolve().toDescriptor());

        List<MethodCallExpr> methodCalls = cu.findAll(MethodCallExpr.class);
        // check descriptor of ReflectionMethodDeclaration
        assertEquals("(Ljava/lang/String;)V", methodCalls.get(0).resolve().toDescriptor());
        // of JavassistMethodDeclaration
        assertEquals("()Ljavassist/ClassPool;", methodCalls.get(1).resolve().toDescriptor());
        // of ValueOfMethod
        assertEquals("(Ljava/lang/String;)LA/TestEnum;", methodCalls.get(2).resolve().toDescriptor());
        // of ValuesMethod
        assertEquals("()[LA/TestEnum;", methodCalls.get(3).resolve().toDescriptor());
    }
}
