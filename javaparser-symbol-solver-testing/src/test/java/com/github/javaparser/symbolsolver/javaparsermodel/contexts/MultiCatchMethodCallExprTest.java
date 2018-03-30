package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

/**
 * Test for issue 1482: https://github.com/javaparser/javaparser/issues/1482
 * When trying to resolve a MethodCallExpr within a multi catch, an UnsupportedOperationException is thrown.
 */
public class MultiCatchMethodCallExprTest extends AbstractResolutionTest {

    @Test
    public void issue1482() {
        CompilationUnit cu = parseSample("Issue1482");
        cu.accept(new Visitor(), null);
    }

    private static class Visitor extends VoidVisitorAdapter<Void> {
        @Override
        public void visit(MethodCallExpr n, Void arg) {
            if (n.getArguments().size() != 0) {
                JavaParserFacade.get(new ReflectionTypeSolver(true)).getType(n.getArgument(0));
            }
        }
    }
}
