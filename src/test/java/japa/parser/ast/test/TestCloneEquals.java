package japa.parser.ast.test;

import org.junit.Test;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.visitor.CloneVisitor;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

public class TestCloneEquals {

  @Test
  public
  void tesCompilationUnitEqual() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
        CompilationUnit cu1 = Helper.parserString(source);
        CompilationUnit cu2 = (CompilationUnit)cu1.accept(new CloneVisitor(), null);
        assertEquals(cu1, cu2);
  }

  @Test
  public
  void tesCompilationUnitNotEqual() throws Exception {
        String source = Helper.readStream(getClass().getResourceAsStream("DumperTestClass.java"));
        CompilationUnit cu1 = Helper.parserString(source);
        CompilationUnit cu2 = (CompilationUnit)cu1.accept(new CloneVisitor(), null);
        cu2.getPackage().getName().setName("some.unique.package");
        assertFalse(cu2.equals(cu1));
  }
}
