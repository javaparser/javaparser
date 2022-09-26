package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;

class CommentRemovalSpacing {

	@Test
    void commentWhitespaceIsRemovedWithComment() {
        String src = 
                "public class Test {\n" + 
                "  /**" +
                "   * Hello." +
                "   */     " +
                "       " +
                "  @MyAnnotation\n" +
                "  public void foo(Bar x, Bar y) {\n" + 
                "  }\n" + 
                "}";
        String expectedResult = 
                "public class Test {\n" + 
                "  @MyAnnotation\n" +
                "  public void foo(Bar x, Bar y) {\n" + 
                "  }\n" + 
                "}";
        
        StaticJavaParser.setConfiguration(new ParserConfiguration().setLexicalPreservationEnabled(true));
        CompilationUnit cu = StaticJavaParser.parse(src);
        LexicalPreservingPrinter.setup(cu);
        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        method.getJavadocComment().get().remove();
        assertEquals(expectedResult, LexicalPreservingPrinter.print(cu));
    }

}
