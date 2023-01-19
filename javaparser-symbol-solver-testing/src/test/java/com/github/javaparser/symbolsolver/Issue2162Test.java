/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.*;

/**
 * @see <a href="https://github.com/javaparser/javaparser/issues/2162">https://github.com/javaparser/javaparser/issues/2162</a>
 */
public class Issue2162Test extends AbstractSymbolResolutionTest {

    private JavaParser javaParser;
    private CompilationUnit cu;
    private TypeSolver typeSolver;
    private ParserConfiguration configuration;
    private List<MethodDeclaration> classMethods;
    private List<MethodCallExpr> methodCallExprs;


    @BeforeEach
    public void setUp() {
        typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver());
        configuration = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        javaParser = new JavaParser(configuration);

        //language=JAVA
        String src = "" +
            "import java.awt.*;\n" +
            "\n" +
            "abstract class Screen <V extends Component> {\n" +
            "    abstract V getView();\n" +
            "}\n" +
            "\n" +
            "class D extends Component {\n" +
            "    void getTest() {\n" +
            "    }\n" +
            "}\n" +
            "\n" +
            "class B extends Screen<D> {\n" +
            "    @Override\n" +
            "    D getView() {\n" +
            "        return new D();\n" +
            "    }\n" +
            "}\n" +
            "\n" +
            "class Run {\n" +
            "    public static void main(String[] args) {\n" +
            "        B b1 = new B();\n" +
            "        b1.getView(); // b1.getView() -> B#getView(), overriding Screen#getView() -> returns object of type D.\n" +
            "        \n" +
            "        // Note that if `b2.getView` is parsed as Screen#getView (as B extends Screen), it will return type `V extends Component` thus will fail to locate the method `Component#getTest()` \n" +
            "        B b2 = new B();\n" +
            "        b2.getView().getTest(); // b2.getView() -> returns object of type D, per above // D#getTest returns void.\n" +
            "        \n" +
            "        // This part is expected to fail as D#getView does not exist (where D is of type `V extends Component`)\n" +
            "        B b3 = new B();\n" +
            "        b3.getView().getView(); // b3.getView() -> returns object of type D, per above // D#getView doesn't exist, thus resolution will fail.\n" +
            "    }\n" +
            "}\n" +
            "";


        ParseResult<CompilationUnit> parseResult = javaParser.parse(
            ParseStart.COMPILATION_UNIT,
            provider(src)
        );


//        parseResult.getProblems().forEach(problem -> System.out.println("problem.getVerboseMessage() = " + problem.getVerboseMessage()));

        assertTrue(parseResult.isSuccessful());
        assertEquals(0, parseResult.getProblems().size(), "Expected zero errors when attempting to parse the input code.");
        assertTrue(parseResult.getResult().isPresent(), "Must have a parse result to run this test.");

        this.cu = parseResult.getResult().get();

        classMethods = this.cu.getClassByName("Run").get().getMethods();
        assertEquals(1, classMethods.size(), "Expected only one class with this matching name.");

        methodCallExprs = classMethods.get(0).findAll(MethodCallExpr.class);
        assertTrue(methodCallExprs.size() > 0, "Expected more than one method call.");
    }


    @Test
    public void doTest_withJavaParserFacade_explicit() {
        JavaParserFacade javaParserFacade = JavaParserFacade.get(this.typeSolver);

//        assertEquals(5, methodCallExprs.size(), "Unexpected number of method calls -- has the test code been updated, without also updating this test case?");

        // b1.getView()
        assertEquals("D", javaParserFacade.solve(methodCallExprs.get(0)).getCorrespondingDeclaration().getReturnType().describe());

        // b2.getView()
        assertEquals("D", javaParserFacade.solve(methodCallExprs.get(2)).getCorrespondingDeclaration().getReturnType().describe());
        // b2.getView().getTest()
        assertEquals("void", javaParserFacade.solve(methodCallExprs.get(1)).getCorrespondingDeclaration().getReturnType().describe());

        // b3.getView()
        assertEquals("D", javaParserFacade.solve(methodCallExprs.get(4)).getCorrespondingDeclaration().getReturnType().describe());
        assertThrows(UnsupportedOperationException.class, () -> {
            // b3.getView().getView() -- causing error
            assertEquals("V", javaParserFacade.solve(methodCallExprs.get(3)).getCorrespondingDeclaration().getReturnType().describe());
        }, "Exected this resolution to fail due to the chained methods -- `getView()` shouldn't exist on the return value from the first call to `getView()`.");

    }


}
