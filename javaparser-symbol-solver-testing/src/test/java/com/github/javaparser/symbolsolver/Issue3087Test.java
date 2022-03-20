package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.fail;

import org.junit.jupiter.api.Test;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

public class Issue3087Test extends AbstractResolutionTest {
    
    @Test
    void testCompilationUnitWithTwoClassesWithTheSameName() {
      // Setup symbol solver
      StaticJavaParser.getConfiguration()
              .setSymbolResolver(
                      new JavaSymbolSolver(new ReflectionTypeSolver())
              );
      // Setup source code
      String sourceCode = "class A {\n" +
              "\n" +
              "    class EntrySetImpl implements EntrySet<Object, Object> {}\n" +
              "\n" +
              "    class Bar {\n" +
              "        private class EntrySet {}\n" +
              "    }\n" +
              "\n" +
              "    interface EntrySet<K, V> {}\n" +
              "\n" +
              "}\n";
      CompilationUnit cu = StaticJavaParser.parse(sourceCode);

      // Resolve the EntrySetImpl class and try to get its ancestors
      ClassOrInterfaceDeclaration coid = cu.findFirst(
              ClassOrInterfaceDeclaration.class,
              c -> c.getNameAsString().equals("EntrySetImpl")
      ).get();
      
      ResolvedReferenceTypeDeclaration resolvedClass = coid.resolve();
      try {
          resolvedClass.getAncestors();
      } catch (IllegalArgumentException e) {
          fail("Unable to resolve class EntrySet<Object, Object>", e);
      }
    }

}
