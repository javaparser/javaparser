package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Assert;
import org.junit.Test;

public class Issue1660 extends AbstractResolutionTest {

    @Test
    public void test() {
        parseSample("Issue1660").accept(new VoidVisitorAdapter<Void>() {
            @Override
            public void visit(MethodCallExpr n, Void arg) {
                SymbolReference<ResolvedMethodDeclaration> solve = JavaParserFacade.get(new ReflectionTypeSolver()).solve(n);
                Assert.assertTrue(solve.isSolved());
                String qualifiedSignature = solve.getCorrespondingDeclaration().getQualifiedSignature();
                Assert.assertEquals("X.Logging.info(java.lang.Object, java.lang.Throwable)", qualifiedSignature);
            }
        }, null);

    }
}
