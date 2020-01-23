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

/**
 * We analyze a more recent version of JavaParser, after the project moved to Java 8.
 */
@SlowTest
class AnalyseNewJavaParserTest extends AbstractResolutionTest {

    private static final Path root = adaptPath("src/test/test_sourcecode/javaparser_new_src");
    private static final Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(
                new ReflectionTypeSolver(),
                new JavaParserTypeSolver(src, new LeanParserConfiguration()),
                new JavaParserTypeSolver(root.resolve("javaparser-generated-sources"), new LeanParserConfiguration()));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        sourceFileInfoExtractor.setVerbose(true);
        return sourceFileInfoExtractor;
    }

    private static SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();

    static String readFile(Path file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(file);
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parse(String fileName) throws IOException {
        Path sourceFile = src.resolve(fileName + ".java");
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solveMethodCalls(sourceFile);
        String output = outErrStream.toString();

        Path expectedOutput = root.resolve("expected_output");
        Path path = expectedOutput.resolve(fileName.replaceAll("/", "_") + ".txt");
        Path dstFile = path;

        if (DEBUG && (sourceFileInfoExtractor.getFailures() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertEquals(0, sourceFileInfoExtractor.getFailures(), "No failures expected when analyzing " + path);
        assertEquals(0, sourceFileInfoExtractor.getUnsupported(), "No UnsupportedOperationException expected when analyzing " + path);

        if (!Files.exists(dstFile)) {
            // If we need to update the file uncomment these lines
            PrintWriter writer = new PrintWriter(dstFile.toAbsolutePath().toFile(), "UTF-8");
            writer.print(output);
            writer.close();
        }

        String expected = readFile(dstFile);

        String[] outputLines = output.split("\n");
        String[] expectedLines = expected.split("\n");

        for (int i = 0; i < Math.min(outputLines.length, expectedLines.length); i++) {
            assertEquals(expectedLines[i].trim(), outputLines[i].trim(), "Line " + (i + 1) + " of " + path + " is different from what is expected");
        }

        assertEquals(expectedLines.length, outputLines.length);

        JavaParserFacade.clearInstances();
    }

    @Test
    void parseUtilsUtils() throws IOException {
        parse("org/javaparser/utils/Utils");
    }

    @Test
    void parseCommentsInserter() throws IOException {
        parse("org/javaparser/CommentsInserter");
    }

    @Test
    void parsePositionUtils() throws IOException {
        parse("org/javaparser/utils/PositionUtils");
    }

    @Test
    void parseModifier() throws IOException {
        parse("org/javaparser/ast/Modifier");
    }

    @Test
    void parseNodeWithMembers() throws IOException {
        parse("org/javaparser/ast/nodeTypes/NodeWithMembers");
    }

    @Test
    void parseAstStmts() throws IOException {
        parse("org/javaparser/ast/stmt/AssertStmt");
        parse("org/javaparser/ast/stmt/BlockStmt");
        parse("org/javaparser/ast/stmt/BreakStmt");
        parse("org/javaparser/ast/stmt/CatchClause");
        parse("org/javaparser/ast/stmt/ContinueStmt");
        parse("org/javaparser/ast/stmt/DoStmt");
        parse("org/javaparser/ast/stmt/EmptyStmt");
        parse("org/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parse("org/javaparser/ast/stmt/ExpressionStmt");
        parse("org/javaparser/ast/stmt/ForStmt");
        parse("org/javaparser/ast/stmt/ForeachStmt");
        parse("org/javaparser/ast/stmt/IfStmt");
        parse("org/javaparser/ast/stmt/LabeledStmt");
        parse("org/javaparser/ast/stmt/ReturnStmt");
        parse("org/javaparser/ast/stmt/Statement");
        parse("org/javaparser/ast/stmt/SwitchEntryStmt");
        parse("org/javaparser/ast/stmt/SwitchStmt");
        parse("org/javaparser/ast/stmt/SynchronizedStmt");
        parse("org/javaparser/ast/stmt/ThrowStmt");
        parse("org/javaparser/ast/stmt/TryStmt");
        parse("org/javaparser/ast/stmt/TypeDeclarationStmt");
        parse("org/javaparser/ast/stmt/WhileStmt");
    }

    @Test
    void parseAstExprs() throws IOException {
        parse("org/javaparser/ast/expr/AnnotationExpr");
        parse("org/javaparser/ast/expr/ArrayAccessExpr");
        parse("org/javaparser/ast/expr/ArrayCreationExpr");
        parse("org/javaparser/ast/expr/ArrayInitializerExpr");
        parse("org/javaparser/ast/expr/AssignExpr");
        parse("org/javaparser/ast/expr/BinaryExpr");
        parse("org/javaparser/ast/expr/BooleanLiteralExpr");
        parse("org/javaparser/ast/expr/CastExpr");
        parse("org/javaparser/ast/expr/CharLiteralExpr");
        parse("org/javaparser/ast/expr/ClassExpr");
        parse("org/javaparser/ast/expr/ConditionalExpr");
        parse("org/javaparser/ast/expr/DoubleLiteralExpr");
        parse("org/javaparser/ast/expr/EnclosedExpr");
        parse("org/javaparser/ast/expr/Expression");
        parse("org/javaparser/ast/expr/FieldAccessExpr");
        parse("org/javaparser/ast/expr/InstanceOfExpr");
        parse("org/javaparser/ast/expr/IntegerLiteralExpr");
        parse("org/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parse("org/javaparser/ast/expr/LambdaExpr");
        parse("org/javaparser/ast/expr/LiteralExpr");
        parse("org/javaparser/ast/expr/LongLiteralExpr");
        parse("org/javaparser/ast/expr/LongLiteralMinValueExpr");
        parse("org/javaparser/ast/expr/MarkerAnnotationExpr");
        parse("org/javaparser/ast/expr/MemberValuePair");
        parse("org/javaparser/ast/expr/MethodCallExpr");
        parse("org/javaparser/ast/expr/MethodReferenceExpr");
        parse("org/javaparser/ast/expr/NameExpr");
        parse("org/javaparser/ast/expr/NormalAnnotationExpr");
        parse("org/javaparser/ast/expr/NullLiteralExpr");
        parse("org/javaparser/ast/expr/ObjectCreationExpr");
        parse("org/javaparser/ast/expr/QualifiedNameExpr");
        parse("org/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parse("org/javaparser/ast/expr/StringLiteralExpr");
        parse("org/javaparser/ast/expr/SuperExpr");
        parse("org/javaparser/ast/expr/ThisExpr");
        parse("org/javaparser/ast/expr/TypeExpr");
        parse("org/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    void parseVariableDeclarationExpr() throws IOException {
        parse("org/javaparser/ast/expr/VariableDeclarationExpr");
    }

    @Test
    void parseAstBody() throws IOException {
        parse("org/javaparser/ast/body/AnnotationDeclaration");
        parse("org/javaparser/ast/body/AnnotationMemberDeclaration");
        parse("org/javaparser/ast/body/BodyDeclaration");
        parse("org/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parse("org/javaparser/ast/body/ConstructorDeclaration");
        parse("org/javaparser/ast/body/EmptyMemberDeclaration");
        parse("org/javaparser/ast/body/EmptyTypeDeclaration");
        parse("org/javaparser/ast/body/EnumConstantDeclaration");
        parse("org/javaparser/ast/body/EnumDeclaration");
        parse("org/javaparser/ast/body/FieldDeclaration");
        parse("org/javaparser/ast/body/InitializerDeclaration");
        parse("org/javaparser/ast/body/MethodDeclaration");
        parse("org/javaparser/ast/body/Parameter");
        parse("org/javaparser/ast/body/TypeDeclaration");
        parse("org/javaparser/ast/body/VariableDeclarator");
        parse("org/javaparser/ast/body/VariableDeclaratorId");
    }

    @Test
    void parseAstComments() throws IOException {
        parse("org/javaparser/ast/comments/BlockComment");
        parse("org/javaparser/ast/comments/Comment");
        parse("org/javaparser/ast/comments/CommentsCollection");
        parse("org/javaparser/ast/comments/JavadocComment");
        parse("org/javaparser/ast/comments/LineComment");
    }

    @Test
    void parseAstCompilationUnit() throws IOException {
        parse("org/javaparser/ast/CompilationUnit");
    }

    @Test
    void parseAstRest() throws IOException {
        parse("org/javaparser/ast/AccessSpecifier");
        parse("org/javaparser/ast/ArrayBracketPair");
        parse("org/javaparser/ast/ArrayCreationLevel");
        parse("org/javaparser/ast/Example");
        parse("org/javaparser/ast/ImportDeclaration");
        parse("org/javaparser/ast/Node");
        parse("org/javaparser/ast/PackageDeclaration");
        parse("org/javaparser/ast/UserDataKey");
    }

    @Test
    void parseAstNodeTypes() throws IOException {
        parse("org/javaparser/ast/nodeTypes/NodeWithAnnotations");
        parse("org/javaparser/ast/nodeTypes/NodeWithBlockStmt");
        parse("org/javaparser/ast/nodeTypes/NodeWithBody");
        parse("org/javaparser/ast/nodeTypes/NodeWithDeclaration");
        parse("org/javaparser/ast/nodeTypes/NodeWithElementType");
        parse("org/javaparser/ast/nodeTypes/NodeWithExtends");
        parse("org/javaparser/ast/nodeTypes/NodeWithImplements");
        parse("org/javaparser/ast/nodeTypes/NodeWithJavaDoc");
        parse("org/javaparser/ast/nodeTypes/NodeWithModifiers");
        parse("org/javaparser/ast/nodeTypes/NodeWithName");
        parse("org/javaparser/ast/nodeTypes/NodeWithParameters");
        parse("org/javaparser/ast/nodeTypes/NodeWithStatements");
        parse("org/javaparser/ast/nodeTypes/NodeWithThrowable");
        parse("org/javaparser/ast/nodeTypes/NodeWithType");
        parse("org/javaparser/ast/nodeTypes/NodeWithTypeArguments");
        parse("org/javaparser/ast/nodeTypes/NodeWithVariables");
    }

    @Test
    void parseAstTypes() throws IOException {
        parse("org/javaparser/ast/type/ArrayType");
        parse("org/javaparser/ast/type/ClassOrInterfaceType");
        parse("org/javaparser/ast/type/IntersectionType");
        parse("org/javaparser/ast/type/PrimitiveType");
        parse("org/javaparser/ast/type/ReferenceType");
        parse("org/javaparser/ast/type/Type");
        parse("org/javaparser/ast/type/TypeParameter");
        parse("org/javaparser/ast/type/UnionType");
        parse("org/javaparser/ast/type/UnknownType");
        parse("org/javaparser/ast/type/VoidType");
        parse("org/javaparser/ast/type/WildcardType");
    }

    @Test
    void parseAstVisitor() throws IOException {
        parse("org/javaparser/ast/visitor/CloneVisitor");
        parse("org/javaparser/ast/visitor/EqualsVisitor");
        parse("org/javaparser/ast/visitor/GenericVisitor");
        parse("org/javaparser/ast/visitor/GenericVisitorAdapter");
        parse("org/javaparser/ast/visitor/ModifierVisitorAdapter");
        parse("org/javaparser/ast/visitor/TreeVisitor");
        parse("org/javaparser/ast/visitor/VoidVisitor");
        parse("org/javaparser/ast/visitor/VoidVisitorAdapter");
    }

    @Test
    void parseDumpVisitor() throws IOException {
        parse("org/javaparser/ast/visitor/DumpVisitor");
    }

    @Test
    void parseUtils() throws IOException {
        parse("org/javaparser/utils/ClassUtils");
        parse("org/javaparser/utils/Pair");
    }

    @Test
    void parseAllOtherNodes() throws IOException {
        parse("org/javaparser/JavaParser");
        parse("org/javaparser/ParseProblemException");
        parse("org/javaparser/ParseResult");
        parse("org/javaparser/ParseStart");
        parse("org/javaparser/ParserConfiguration");
        parse("org/javaparser/Position");
        parse("org/javaparser/Problem");
        parse("org/javaparser/Providers");
        parse("org/javaparser/Range");
    }

}
