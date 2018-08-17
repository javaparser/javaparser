package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class Issue343 extends AbstractResolutionTest{

    private TypeSolver typeResolver;
    private JavaParserFacade javaParserFacade;

    private ResolvedType getExpressionType(TypeSolver typeSolver, Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @Before
    public void setup() {
        typeResolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeResolver);
    }

    @Test
    public void resolveStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(String.class), getExpressionType(typeResolver, new StringLiteralExpr("")));
    }

    @Test
    public void resolveIntegerLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new IntegerLiteralExpr(2)));
    }

    @Test(expected = IllegalStateException.class)
    public void toResolveDoubleWeNeedTheAST() {
        getExpressionType(typeResolver, JavaParser.parseExpression("new Double[]{2.0d, 3.0d}[1]"));
    }


    @Test(expected = IllegalStateException.class)
    public void toResolveFloatWeNeedTheAST() {
        getExpressionType(typeResolver, JavaParser.parseExpression("new Float[]{2.0d, 3.0d}"));
    }

    @Test
    public void resolveMethodCallOnStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new MethodCallExpr(new StringLiteralExpr("hello"), "length")));
    }

    @Test(expected = IllegalStateException.class)
    public void resolveLocaleOutsideAST() {
        getExpressionType(typeResolver, new FieldAccessExpr(new NameExpr("Locale"), "US"));
    }
}
