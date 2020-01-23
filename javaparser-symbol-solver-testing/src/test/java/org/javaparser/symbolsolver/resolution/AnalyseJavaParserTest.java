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

package org.javaparser.symbolsolver.resolution;

import org.javaparser.SlowTest;
import org.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import org.javaparser.symbolsolver.SourceFileInfoExtractor;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

@SlowTest
class AnalyseJavaParserTest extends AbstractSymbolResolutionTest {

    private static final Path root = adaptPath("src/test/test_sourcecode/javaparser_src");
    private static final Path properSrc = root.resolve("proper_source");

    private SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(
                new ReflectionTypeSolver(),
                new JavaParserTypeSolver(properSrc, new LeanParserConfiguration()),
                new JavaParserTypeSolver(root.resolve("generated"), new LeanParserConfiguration()));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        return sourceFileInfoExtractor;
    }

    private static String readFile(Path file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(file);
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parse(String fileName) throws IOException {
        Path sourceFile = properSrc.resolve( fileName + ".java");
        SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solve(sourceFile);
        String output = outErrStream.toString();

        String path = "expected_output/" + fileName.replaceAll("/", "_") + ".txt";
        Path dstFile = adaptPath(root.resolve(path));

        if (DEBUG && (sourceFileInfoExtractor.getFailures() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertEquals(0, sourceFileInfoExtractor.getFailures(), "No failures expected when analyzing " + path);
        assertEquals(0, sourceFileInfoExtractor.getUnsupported(), "No UnsupportedOperationException expected when analyzing " + path);

        String expected = readFile(dstFile);

        String[] outputLines = output.split("\n");
        String[] expectedLines = expected.split("\n");

        for (int i = 0; i < Math.min(outputLines.length, expectedLines.length); i++) {
            assertEquals(expectedLines[i].trim(), outputLines[i].trim(), "Line " + (i + 1) + " of " + path + " is different from what is expected");
        }

        assertEquals(expectedLines.length, outputLines.length);

        JavaParserFacade.clearInstances();

        // If we need to update the file uncomment these lines
        //PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
        //writer.print(output);
        //writer.close();
    }

    @Test
    void parsePositionUtils() throws IOException {
        parse("org/javaparser/PositionUtils");
    }

    @Test
    void parseJavaParser() throws IOException {
        parse("org/javaparser/JavaParser");
    }

    @Test
    void parseStatement() throws IOException {
        parse("org/javaparser/ast/stmt/Statement");
    }

    @Test
    void parseCatchClause() throws IOException {
        parse("org/javaparser/ast/stmt/CatchClause");
    }

    @Test
    void parseStatements() throws IOException {
        parse("org/javaparser/ast/stmt/LabeledStmt");
        parse("org/javaparser/ast/stmt/BreakStmt");
        parse("org/javaparser/ast/stmt/ReturnStmt");
        parse("org/javaparser/ast/stmt/DoStmt");
        parse("org/javaparser/ast/stmt/AssertStmt");
        parse("org/javaparser/ast/stmt/ContinueStmt");
        parse("org/javaparser/ast/stmt/BlockStmt");
        parse("org/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parse("org/javaparser/ast/stmt/ExpressionStmt");
        parse("org/javaparser/ast/stmt/EmptyStmt");
        parse("org/javaparser/ast/stmt/SwitchStmt");
        parse("org/javaparser/ast/stmt/IfStmt");
        parse("org/javaparser/ast/stmt/SwitchEntryStmt");
        parse("org/javaparser/ast/stmt/SynchronizedStmt");
        parse("org/javaparser/ast/stmt/ForeachStmt");
        parse("org/javaparser/ast/stmt/ForStmt");
        parse("org/javaparser/ast/stmt/WhileStmt");
        parse("org/javaparser/ast/stmt/ThrowStmt");
        parse("org/javaparser/ast/stmt/TryStmt");
        parse("org/javaparser/ast/stmt/TypeDeclarationStmt");
    }

    @Test
    void parseExpressions() throws IOException {
        parse("org/javaparser/ast/expr/NameExpr");
        parse("org/javaparser/ast/expr/FieldAccessExpr");
        parse("org/javaparser/ast/expr/CharLiteralExpr");
        parse("org/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parse("org/javaparser/ast/expr/IntegerLiteralExpr");
        parse("org/javaparser/ast/expr/ArrayCreationExpr");
        parse("org/javaparser/ast/expr/VariableDeclarationExpr");
        parse("org/javaparser/ast/expr/SuperExpr");
        parse("org/javaparser/ast/expr/ArrayInitializerExpr");
        parse("org/javaparser/ast/expr/EnclosedExpr");
        parse("org/javaparser/ast/expr/Expression");
        parse("org/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parse("org/javaparser/ast/expr/MethodReferenceExpr");
        parse("org/javaparser/ast/expr/ThisExpr");
        parse("org/javaparser/ast/expr/LiteralExpr");
        parse("org/javaparser/ast/expr/AnnotationExpr");
        parse("org/javaparser/ast/expr/InstanceOfExpr");
        parse("org/javaparser/ast/expr/LongLiteralExpr");
        parse("org/javaparser/ast/expr/StringLiteralExpr");
        parse("org/javaparser/ast/expr/NullLiteralExpr");
        parse("org/javaparser/ast/expr/ObjectCreationExpr");
        parse("org/javaparser/ast/expr/TypeExpr");
        parse("org/javaparser/ast/expr/DoubleLiteralExpr");
        parse("org/javaparser/ast/expr/LongLiteralMinValueExpr");
        parse("org/javaparser/ast/expr/MarkerAnnotationExpr");
        parse("org/javaparser/ast/expr/LambdaExpr");
        parse("org/javaparser/ast/expr/AssignExpr");
        parse("org/javaparser/ast/expr/NormalAnnotationExpr");
        parse("org/javaparser/ast/expr/QualifiedNameExpr");
        parse("org/javaparser/ast/expr/MemberValuePair");
        parse("org/javaparser/ast/expr/ArrayAccessExpr");
        parse("org/javaparser/ast/expr/ClassExpr");
        parse("org/javaparser/ast/expr/MethodCallExpr");
        parse("org/javaparser/ast/expr/ConditionalExpr");
        parse("org/javaparser/ast/expr/CastExpr");
        parse("org/javaparser/ast/expr/BooleanLiteralExpr");
        parse("org/javaparser/ast/expr/BinaryExpr");
        parse("org/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    void parseTypes() throws IOException {
        parse("org/javaparser/ast/type/ClassOrInterfaceType");
        parse("org/javaparser/ast/type/PrimitiveType");
        parse("org/javaparser/ast/type/WildcardType");
        parse("org/javaparser/ast/type/UnknownType");
        parse("org/javaparser/ast/type/ReferenceType");
        parse("org/javaparser/ast/type/VoidType");
        parse("org/javaparser/ast/type/Type");
    }

    @Test
    void parseVisitors() throws IOException {
        parse("org/javaparser/ast/visitor/EqualsVisitor");
        parse("org/javaparser/ast/visitor/ModifierVisitorAdapter");
        parse("org/javaparser/ast/visitor/DumpVisitor");
        parse("org/javaparser/ast/visitor/VoidVisitor");
        parse("org/javaparser/ast/visitor/GenericVisitor");
        parse("org/javaparser/ast/visitor/VoidVisitorAdapter");
        parse("org/javaparser/ast/visitor/GenericVisitorAdapter");
    }

    @Test
    void parseCloneVisitor() throws IOException {
        parse("org/javaparser/ast/visitor/CloneVisitor");
    }

    @Test
    void parseSourcesHelper() throws IOException {
        parse("org/javaparser/SourcesHelper");
    }

    @Test
    void parseComments() throws IOException {
        parse("org/javaparser/ast/comments/LineComment");
        parse("org/javaparser/ast/comments/Comment");
        parse("org/javaparser/ast/comments/CommentsParser");
        parse("org/javaparser/ast/comments/JavadocComment");
        parse("org/javaparser/ast/comments/BlockComment");
        parse("org/javaparser/ast/comments/CommentsCollection");
    }

    @Test
    void parseTheRest() throws IOException {
        parse("org/javaparser/ast/internal/Utils");
        parse("org/javaparser/ast/body/AnnotationMemberDeclaration");
        parse("org/javaparser/ast/body/EnumDeclaration");
        parse("org/javaparser/ast/body/Parameter");
        parse("org/javaparser/ast/body/EnumConstantDeclaration");
        parse("org/javaparser/ast/body/VariableDeclarator");
        parse("org/javaparser/ast/body/TypeDeclaration");
        parse("org/javaparser/ast/body/EmptyMemberDeclaration");
        parse("org/javaparser/ast/body/ModifierSet");
        parse("org/javaparser/ast/body/VariableDeclaratorId");
        parse("org/javaparser/ast/body/BaseParameter");
        parse("org/javaparser/ast/body/AnnotableNode");
        parse("org/javaparser/ast/body/AnnotationDeclaration");
        parse("org/javaparser/ast/body/MethodDeclaration");
        parse("org/javaparser/ast/body/EmptyTypeDeclaration");
        parse("org/javaparser/ast/body/InitializerDeclaration");
        parse("org/javaparser/ast/body/BodyDeclaration");
        parse("org/javaparser/ast/body/FieldDeclaration");
        parse("org/javaparser/ast/body/ConstructorDeclaration");
        parse("org/javaparser/ast/body/WithDeclaration");
        parse("org/javaparser/ast/body/MultiTypeParameter");
        parse("org/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parse("org/javaparser/ast/TreeVisitor");
        parse("org/javaparser/ast/PackageDeclaration");
        parse("org/javaparser/ast/DocumentableNode");
        parse("org/javaparser/ast/NamedNode");
        parse("org/javaparser/ast/Node");
        parse("org/javaparser/ast/AccessSpecifier");
        parse("org/javaparser/ast/CompilationUnit");
        parse("org/javaparser/ast/TypeParameter");
        parse("org/javaparser/ast/ImportDeclaration");
        parse("org/javaparser/Position");
        parse("org/javaparser/ASTHelper");
    }

}
