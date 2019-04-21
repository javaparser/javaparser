package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class Issue343Test extends AbstractResolutionTest{

    private TypeSolver typeResolver;
    private JavaParserFacade javaParserFacade;

    private ResolvedType getExpressionType(TypeSolver typeSolver, Expression expression) {
        return JavaParserFacade.get(typeSolver).getType(expression);
    }

    @BeforeEach
    void setup() {
        typeResolver = new ReflectionTypeSolver();
        javaParserFacade = JavaParserFacade.get(typeResolver);
    }

    @Test
    void resolveStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(String.class), getExpressionType(typeResolver, new StringLiteralExpr("")));
    }

    @Test
    void resolveIntegerLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new IntegerLiteralExpr(2)));
    }

    @Test
    void toResolveDoubleWeNeedTheAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, parseExpression("new Double[]{2.0d, 3.0d}[1]")));
    }


    @Test
    void toResolveFloatWeNeedTheAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, parseExpression("new Float[]{2.0d, 3.0d}")));
    }

    @Test
    void resolveMethodCallOnStringLiteralOutsideAST() {
        assertEquals(javaParserFacade.classToResolvedType(int.class), getExpressionType(typeResolver, new MethodCallExpr(new StringLiteralExpr("hello"), "length")));
    }

    @Test
    void resolveLocaleOutsideAST() {
        assertThrows(IllegalStateException.class, () -> getExpressionType(typeResolver, new FieldAccessExpr(new NameExpr("Locale"), "US")));
    }
}
