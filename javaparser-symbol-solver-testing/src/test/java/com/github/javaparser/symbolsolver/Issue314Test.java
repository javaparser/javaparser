package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Issue314Test extends AbstractResolutionTest{

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
    void resolveReferenceToFieldInheritedByInterface() {
        String code = "package foo.bar;\n"+
                "interface  A {\n" +
                "        int a = 0;\n" +
                "    }\n" +
                "    \n" +
                "    class B implements A {\n" +
                "        int getA() {\n" +
                "            return a;\n" +
                "        }\n" +
                "    }";
        CompilationUnit cu = parse(code);
        NameExpr refToA = Navigator.findNameExpression(Navigator.demandClass(cu, "B"), "a").get();
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = javaParserFacade.solve(refToA);
        assertEquals(true, symbolReference.isSolved());
        assertEquals(true, symbolReference.getCorrespondingDeclaration().isField());
        assertEquals("a", symbolReference.getCorrespondingDeclaration().getName());
    }



}
