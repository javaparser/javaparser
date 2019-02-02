/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.SlowTest;
import com.github.javaparser.symbolsolver.SourceFileInfoExtractor;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
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

        if (isJavaVersion9OrAbove()) {
            Path path9 = expectedOutput.resolve(fileName.replaceAll("/", "_") + "_J9.txt");
            Path dstFile9 = path9;
            if (Files.exists(dstFile9)) {
                path = path9;
                dstFile = dstFile9;
            }
        }

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
        parse("com/github/javaparser/utils/Utils");
    }

    @Test
    void parseCommentsInserter() throws IOException {
        parse("com/github/javaparser/CommentsInserter");
    }

    @Test
    void parsePositionUtils() throws IOException {
        parse("com/github/javaparser/utils/PositionUtils");
    }

    @Test
    void parseModifier() throws IOException {
        parse("com/github/javaparser/ast/Modifier");
    }

    @Test
    void parseNodeWithMembers() throws IOException {
        parse("com/github/javaparser/ast/nodeTypes/NodeWithMembers");
    }

    @Test
    void parseAstStmts() throws IOException {
        parse("com/github/javaparser/ast/stmt/AssertStmt");
        parse("com/github/javaparser/ast/stmt/BlockStmt");
        parse("com/github/javaparser/ast/stmt/BreakStmt");
        parse("com/github/javaparser/ast/stmt/CatchClause");
        parse("com/github/javaparser/ast/stmt/ContinueStmt");
        parse("com/github/javaparser/ast/stmt/DoStmt");
        parse("com/github/javaparser/ast/stmt/EmptyStmt");
        parse("com/github/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parse("com/github/javaparser/ast/stmt/ExpressionStmt");
        parse("com/github/javaparser/ast/stmt/ForStmt");
        parse("com/github/javaparser/ast/stmt/ForeachStmt");
        parse("com/github/javaparser/ast/stmt/IfStmt");
        parse("com/github/javaparser/ast/stmt/LabeledStmt");
        parse("com/github/javaparser/ast/stmt/ReturnStmt");
        parse("com/github/javaparser/ast/stmt/Statement");
        parse("com/github/javaparser/ast/stmt/SwitchEntryStmt");
        parse("com/github/javaparser/ast/stmt/SwitchStmt");
        parse("com/github/javaparser/ast/stmt/SynchronizedStmt");
        parse("com/github/javaparser/ast/stmt/ThrowStmt");
        parse("com/github/javaparser/ast/stmt/TryStmt");
        parse("com/github/javaparser/ast/stmt/TypeDeclarationStmt");
        parse("com/github/javaparser/ast/stmt/WhileStmt");
    }

    @Test
    void parseAstExprs() throws IOException {
        parse("com/github/javaparser/ast/expr/AnnotationExpr");
        parse("com/github/javaparser/ast/expr/ArrayAccessExpr");
        parse("com/github/javaparser/ast/expr/ArrayCreationExpr");
        parse("com/github/javaparser/ast/expr/ArrayInitializerExpr");
        parse("com/github/javaparser/ast/expr/AssignExpr");
        parse("com/github/javaparser/ast/expr/BinaryExpr");
        parse("com/github/javaparser/ast/expr/BooleanLiteralExpr");
        parse("com/github/javaparser/ast/expr/CastExpr");
        parse("com/github/javaparser/ast/expr/CharLiteralExpr");
        parse("com/github/javaparser/ast/expr/ClassExpr");
        parse("com/github/javaparser/ast/expr/ConditionalExpr");
        parse("com/github/javaparser/ast/expr/DoubleLiteralExpr");
        parse("com/github/javaparser/ast/expr/EnclosedExpr");
        parse("com/github/javaparser/ast/expr/Expression");
        parse("com/github/javaparser/ast/expr/FieldAccessExpr");
        parse("com/github/javaparser/ast/expr/InstanceOfExpr");
        parse("com/github/javaparser/ast/expr/IntegerLiteralExpr");
        parse("com/github/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parse("com/github/javaparser/ast/expr/LambdaExpr");
        parse("com/github/javaparser/ast/expr/LiteralExpr");
        parse("com/github/javaparser/ast/expr/LongLiteralExpr");
        parse("com/github/javaparser/ast/expr/LongLiteralMinValueExpr");
        parse("com/github/javaparser/ast/expr/MarkerAnnotationExpr");
        parse("com/github/javaparser/ast/expr/MemberValuePair");
        parse("com/github/javaparser/ast/expr/MethodCallExpr");
        parse("com/github/javaparser/ast/expr/MethodReferenceExpr");
        parse("com/github/javaparser/ast/expr/NameExpr");
        parse("com/github/javaparser/ast/expr/NormalAnnotationExpr");
        parse("com/github/javaparser/ast/expr/NullLiteralExpr");
        parse("com/github/javaparser/ast/expr/ObjectCreationExpr");
        parse("com/github/javaparser/ast/expr/QualifiedNameExpr");
        parse("com/github/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parse("com/github/javaparser/ast/expr/StringLiteralExpr");
        parse("com/github/javaparser/ast/expr/SuperExpr");
        parse("com/github/javaparser/ast/expr/ThisExpr");
        parse("com/github/javaparser/ast/expr/TypeExpr");
        parse("com/github/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    void parseVariableDeclarationExpr() throws IOException {
        parse("com/github/javaparser/ast/expr/VariableDeclarationExpr");
    }

    @Test
    void parseAstBody() throws IOException {
        parse("com/github/javaparser/ast/body/AnnotationDeclaration");
        parse("com/github/javaparser/ast/body/AnnotationMemberDeclaration");
        parse("com/github/javaparser/ast/body/BodyDeclaration");
        parse("com/github/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parse("com/github/javaparser/ast/body/ConstructorDeclaration");
        parse("com/github/javaparser/ast/body/EmptyMemberDeclaration");
        parse("com/github/javaparser/ast/body/EmptyTypeDeclaration");
        parse("com/github/javaparser/ast/body/EnumConstantDeclaration");
        parse("com/github/javaparser/ast/body/EnumDeclaration");
        parse("com/github/javaparser/ast/body/FieldDeclaration");
        parse("com/github/javaparser/ast/body/InitializerDeclaration");
        parse("com/github/javaparser/ast/body/MethodDeclaration");
        parse("com/github/javaparser/ast/body/Parameter");
        parse("com/github/javaparser/ast/body/TypeDeclaration");
        parse("com/github/javaparser/ast/body/VariableDeclarator");
        parse("com/github/javaparser/ast/body/VariableDeclaratorId");
    }

    @Test
    void parseAstComments() throws IOException {
        parse("com/github/javaparser/ast/comments/BlockComment");
        parse("com/github/javaparser/ast/comments/Comment");
        parse("com/github/javaparser/ast/comments/CommentsCollection");
        parse("com/github/javaparser/ast/comments/JavadocComment");
        parse("com/github/javaparser/ast/comments/LineComment");
    }

    @Test
    void parseAstCompilationUnit() throws IOException {
        parse("com/github/javaparser/ast/CompilationUnit");
    }

    @Test
    void parseAstRest() throws IOException {
        parse("com/github/javaparser/ast/AccessSpecifier");
        parse("com/github/javaparser/ast/ArrayBracketPair");
        parse("com/github/javaparser/ast/ArrayCreationLevel");
        parse("com/github/javaparser/ast/Example");
        parse("com/github/javaparser/ast/ImportDeclaration");
        parse("com/github/javaparser/ast/Node");
        parse("com/github/javaparser/ast/PackageDeclaration");
        parse("com/github/javaparser/ast/UserDataKey");
    }

    @Test
    void parseAstNodeTypes() throws IOException {
        parse("com/github/javaparser/ast/nodeTypes/NodeWithAnnotations");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithBlockStmt");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithBody");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithDeclaration");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithElementType");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithExtends");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithImplements");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithJavaDoc");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithModifiers");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithName");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithParameters");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithStatements");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithThrowable");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithType");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithTypeArguments");
        parse("com/github/javaparser/ast/nodeTypes/NodeWithVariables");
    }

    @Test
    void parseAstTypes() throws IOException {
        parse("com/github/javaparser/ast/type/ArrayType");
        parse("com/github/javaparser/ast/type/ClassOrInterfaceType");
        parse("com/github/javaparser/ast/type/IntersectionType");
        parse("com/github/javaparser/ast/type/PrimitiveType");
        parse("com/github/javaparser/ast/type/ReferenceType");
        parse("com/github/javaparser/ast/type/Type");
        parse("com/github/javaparser/ast/type/TypeParameter");
        parse("com/github/javaparser/ast/type/UnionType");
        parse("com/github/javaparser/ast/type/UnknownType");
        parse("com/github/javaparser/ast/type/VoidType");
        parse("com/github/javaparser/ast/type/WildcardType");
    }

    @Test
    void parseAstVisitor() throws IOException {
        parse("com/github/javaparser/ast/visitor/CloneVisitor");
        parse("com/github/javaparser/ast/visitor/EqualsVisitor");
        parse("com/github/javaparser/ast/visitor/GenericVisitor");
        parse("com/github/javaparser/ast/visitor/GenericVisitorAdapter");
        parse("com/github/javaparser/ast/visitor/ModifierVisitorAdapter");
        parse("com/github/javaparser/ast/visitor/TreeVisitor");
        parse("com/github/javaparser/ast/visitor/VoidVisitor");
        parse("com/github/javaparser/ast/visitor/VoidVisitorAdapter");
    }

    @Test
    void parseDumpVisitor() throws IOException {
        parse("com/github/javaparser/ast/visitor/DumpVisitor");
    }

    @Test
    void parseUtils() throws IOException {
        parse("com/github/javaparser/utils/ClassUtils");
        parse("com/github/javaparser/utils/Pair");
    }

    @Test
    void parseAllOtherNodes() throws IOException {
        parse("com/github/javaparser/JavaParser");
        parse("com/github/javaparser/ParseProblemException");
        parse("com/github/javaparser/ParseResult");
        parse("com/github/javaparser/ParseStart");
        parse("com/github/javaparser/ParserConfiguration");
        parse("com/github/javaparser/Position");
        parse("com/github/javaparser/Problem");
        parse("com/github/javaparser/Providers");
        parse("com/github/javaparser/Range");
    }

}
