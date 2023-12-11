package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ParserConfiguration.LanguageLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;

class Issue4245Test extends AbstractLexicalPreservingTest  {

	@Test
    public void test() {

    	ParserConfiguration parserConfiguration = new ParserConfiguration();
		parserConfiguration.setLanguageLevel(LanguageLevel.JAVA_17);
		StaticJavaParser.setConfiguration(parserConfiguration);
		considerCode(
    			"public sealed interface IUpdatePortCommand permits UpdateScheduleCommand, UpdateStateCommand {}");

		ClassOrInterfaceDeclaration classOrInterface = cu.findFirst(ClassOrInterfaceDeclaration.class).get();
		classOrInterface.setModifiers();

        String expected =
        		"interface IUpdatePortCommand permits UpdateScheduleCommand, UpdateStateCommand {}";

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

}
