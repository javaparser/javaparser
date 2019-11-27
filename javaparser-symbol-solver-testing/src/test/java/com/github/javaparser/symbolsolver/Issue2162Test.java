/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.Providers.provider;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/*
 * https://github.com/javaparser/javaparser/issues/2162
 *
 * I'm trying to solve the generic return type of a `MethodCallExpr`.
 * e.g.: `getView().getTest()`, where `getView()` returns `V` with the superclass `AWT.Component`.
 *
 *  I'm using `JavaParserFacade.solve(methodCallExpr).getCorrespondingDeclaration().getReturnType()`, where `methodCallExpr` is the expression above (`getView().getTest()`).
 * `getView()` is resolved in the type `AWT.Component`, which does not obviously has a method called `getTest`.
 *
 * I get `java.lang.RuntimeException: Unable to calculate the type of a parameter of a method call`.
 *
 * getView() // B#getView
 * getView().getTest()) // D#getTest -- inherited from abstract class Screen
 *
 *
 * {@code
      import java.awt.*;

      abstract class Screen <V extends Component> {
          abstract V getView();
      }

      class D extends Component {
          void getTest() {
          }
      }

      class B extends Screen<D> {
          @Override
          D getView() {
              return new D();
          }
      }
 * }
 *
 */
public class Issue2162Test extends AbstractSymbolResolutionTest {

    private JavaParser javaParser;
    private CompilationUnit cu;
    private TypeSolver typeSolver;
    private ParserConfiguration configuration;
    private List<MethodDeclaration> classMethods;
    private List<MethodCallExpr> methodCallExprs;


    @BeforeEach
    void setUp() {
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
            "  public static void main(String[] args) {\n" +
            "    B b1 = new B();\n" +
            "    b1.getView(); // B#getView --- method is directly on class B\n" +
            "    \n" +
            "    B b2 = new B();\n" +
            "    b2.getView().getTest(); // D#getTest -- method directly on class D (return value of getView())\n" +
            "    \n" +
            "    // Part of code that attempts to call an inherited method (whose return type JP will attempt to resolve)\n" +
            "    B b3 = new B();\n" +
            "    b3.getView().getView(); // D#getView -- method inherited from abstract class Screen\n" +
            "  }\n" +
            "}\n" +
            "";


        ParseResult<CompilationUnit> parseResult = javaParser.parse(
            ParseStart.COMPILATION_UNIT,
            provider(src)
        );


        System.out.println("parseResult = " + parseResult);
        parseResult.getProblems().forEach(problem -> System.out.println("problem.getVerboseMessage() = " + problem.getVerboseMessage()));

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
    public void doTest_resolveMethod() {
        List<String> errorMessages = new ArrayList<>();
        for (int i = 0; i < methodCallExprs.size(); i++) {
            MethodCallExpr methodCallExpr = methodCallExprs.get(i);
            System.out.println();
            System.out.println("methodCallExpr #" + i + "= " + methodCallExpr);
            try {
                ResolvedMethodDeclaration resolvedMethodDeclaration = methodCallExpr.resolve();
                System.out.println("resolvedMethodDeclaration.getReturnType().describe() = " + resolvedMethodDeclaration.getReturnType().describe());
            } catch (UnsolvedSymbolException e) {
                String errMessage = "Unexpectedly unable to resolve method call #" + i + "\n --> " + methodCallExpr;
                errorMessages.add(errMessage);
            }
        }

        // Print out the collected error messages (if any)
        printErrorMessagesIfPresent(errorMessages);

        assertEquals(0, errorMessages.size(), "Expecting zero error messages. See log for details.");
    }

    @Test
    public void doTest_calculateResolvedType() {
        List<String> errorMessages = new ArrayList<>();
        for (int i = 0; i < methodCallExprs.size(); i++) {
            MethodCallExpr methodCallExpr = methodCallExprs.get(i);
            System.out.println();
            System.out.println("methodCallExpr #" + i + "= " + methodCallExpr);

            try {
                ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
                System.out.println("resolvedType.describe() = " + resolvedType.describe());
            } catch (UnsolvedSymbolException e) {
                String errMessage = "Unexpectedly unable to resolve method call #" + i + "\n --> " + methodCallExpr;
                errorMessages.add(errMessage);
            }
        }

        // Print out the collected error messages (if any)
        printErrorMessagesIfPresent(errorMessages);

        assertEquals(0, errorMessages.size(), "Expecting zero error messages. See log for details.");
    }


    @Test
    public void doTest_withJavaParserFacade() {

        JavaParserFacade javaParserFacade = JavaParserFacade.get(this.typeSolver);

        List<String> errorMessages = new ArrayList<>();
        for (int i = 0; i < methodCallExprs.size(); i++) {
            MethodCallExpr methodCallExpr = methodCallExprs.get(i);
            System.out.println();
            System.out.println("methodCallExpr #" + i + "= " + methodCallExpr);

            SymbolReference<ResolvedMethodDeclaration> solved;
            ResolvedMethodDeclaration correspondingDeclaration;
            ResolvedType returnType;

            // Try/Catch each stage of the call to:
            // javaParserFacade.solve(methodCallExpr).getCorrespondingDeclaration().getReturnType()
            try {
                solved = javaParserFacade.solve(methodCallExpr);
                if (!solved.isSolved()) {
                    System.err.println("Unexpectedly unsolved methodCallExpr");
                }

                try {
                    correspondingDeclaration = solved.getCorrespondingDeclaration();
                    try {
                        returnType = correspondingDeclaration.getReturnType();
                        System.out.println("returnType.describe() = " + returnType.describe());

                    } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
                        String errMessage = "Unexpectedly unable to get return type for method call #" + i + "\n --> " + methodCallExpr + "\n --> solved.isSolved() = " + solved.isSolved();
                        errorMessages.add(errMessage);
                    }

                } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
                    String errMessage = "Unexpectedly unable to get corresponding declaration for method call #" + i + "\n --> " + methodCallExpr;
                    errorMessages.add(errMessage);
                }

            } catch (UnsolvedSymbolException | UnsupportedOperationException e) {
                String errMessage = "Unexpectedly unable to resolve method call #" + i + "\n --> " + methodCallExpr;
                errorMessages.add(errMessage);
            }
        }

        // Print out the collected error messages (if any)
        printErrorMessagesIfPresent(errorMessages);

        assertEquals(0, errorMessages.size(), "Expecting zero error messages. See log for details.");

    }


    @Test
    public void doTest_withJavaParserFacade_explicit() {
        JavaParserFacade javaParserFacade = JavaParserFacade.get(this.typeSolver);

        // b1.getView()
        assertEquals("D", javaParserFacade.solve(methodCallExprs.get(0)).getCorrespondingDeclaration().getReturnType().describe());

        // b2.getView().getTest() -- causing error
        assertEquals("void", javaParserFacade.solve(methodCallExprs.get(1)).getCorrespondingDeclaration().getReturnType().describe());
        // b2.getView()
        assertEquals("D", javaParserFacade.solve(methodCallExprs.get(2)).getCorrespondingDeclaration().getReturnType().describe());

    }


    private void printErrorMessagesIfPresent(List<String> errorMessages) {
        if (errorMessages.size() > 0) {
            System.err.println();
            System.err.println();
            System.err.println("ERRORS: ");
        }
        for (int i = 0; i < errorMessages.size(); i++) {
            String errorMessage = errorMessages.get(i);
            System.err.println("ERROR #" + i + ": " + errorMessage);
        }
    }

}
