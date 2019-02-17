package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * See issue #17
 */
class ArrayExprTest {

    @Test
    void verifyAnArrayAccessExprTypeIsCalculatedProperly() {
        String code = "class A { String[] arrSQL; String toExamine = arrSQL[1]; }";
        FieldDeclaration field = parse(code).getClassByName("A").get().getFieldByName("toExamine").get();

        ResolvedType type = JavaParserFacade.get(new ReflectionTypeSolver()).getType(field.getVariables().get(0).getInitializer().get());
        assertTrue(type.isReferenceType());
        assertEquals("java.lang.String", type.asReferenceType().getQualifiedName());
    }

    @Test
    void arrayLengthValueDeclaration() {
        String code = "class A { String[] arrSQL; int l = arrSQL.length; }";
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(parserConfiguration).parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();
        FieldDeclaration field = cu.getClassByName("A").get().getFieldByName("l").get();

        ResolvedValueDeclaration resolvedValueDeclaration = ((FieldAccessExpr)field.getVariables().get(0).getInitializer().get()).resolve();
        assertEquals("length", resolvedValueDeclaration.getName());
        assertEquals(ResolvedPrimitiveType.INT, resolvedValueDeclaration.getType());
    }
}
