package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.*;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserSymbolDeclarationTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();

    /**
     * Try to create a field using {@link JavaParserSymbolDeclaration#field(VariableDeclarator, TypeSolver)} and check
     * if the returned declaration is marked as a field and can be converted converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration} using {@link ResolvedValueDeclaration#asField()}.
     */
    @Test
    void createdFieldShouldBeMarkedAsField() {
        VariableDeclarator variableDeclarator = parseBodyDeclaration("private final int x = 0;")
                .asFieldDeclaration()
                .getVariable(0);
        ResolvedValueDeclaration field = JavaParserSymbolDeclaration.field(variableDeclarator, typeSolver);

        assertTrue(field.isField());
        assertDoesNotThrow(field::asField);
    }

    /**
     * Try to create a parameter using {@link JavaParserSymbolDeclaration#parameter(Parameter, TypeSolver)} and check
     * if the returned declaration is marked as a parameter and can be converted converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration} using {@link ResolvedValueDeclaration#asParameter()}.
     */
    @Test
    void createdParameterShouldBeMarkedAsParameter() {
        Parameter parameter = parseParameter("String myStr");;
        ResolvedValueDeclaration parameterDeclaration = JavaParserSymbolDeclaration.parameter(parameter, typeSolver);

        assertTrue(parameterDeclaration.isParameter());
        assertDoesNotThrow(parameterDeclaration::asParameter);
    }

    /**
     * Try to create a local variable using {@link JavaParserSymbolDeclaration#localVar(VariableDeclarator, TypeSolver)}
     * and check if the returned declaration is marked as a variable.
     */
    @Test
    void createdLocalVariableShouldBeMarkedAsVariable() {
        VariableDeclarator variableDeclarator = parseVariableDeclarationExpr("int x = 0").getVariable(0);
        ResolvedValueDeclaration localVar = JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver);

        assertTrue(localVar.isVariable());
    }

    /**
     * Try to create a pattern variable using {@link JavaParserSymbolDeclaration#patternVar(PatternExpr, TypeSolver)} and check
     * if the returned declaration is marked as a pattern and can be converted converted to a
     * {@link com.github.javaparser.resolution.declarations.ResolvedPatternDeclaration} using {@link ResolvedValueDeclaration#asPattern()}.
     */
    @Test
    void createdPatternVariableShouldBeMarkedAsPatternVar() {
        PatternExpr patternExpr = new PatternExpr();
        ResolvedValueDeclaration patternVar = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);

        assertTrue(patternVar.isPattern());
        assertDoesNotThrow(patternVar::asPattern);
    }

}
