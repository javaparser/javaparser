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
import org.junit.Test;
import org.junit.experimental.categories.Category;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * We analyze a more recent version of JavaParser, after the project moved to Java 8.
 */
@Category(SlowTest.class)
public class AnalyseNewJavaParserTest extends AbstractResolutionTest {

    private static final Path root = adaptPath("src/test/test_sourcecode/javaparser_new_src");
    private static final Path src = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(root.resolve("javaparser-generated-sources")));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
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

    private void parseFile(String fileName) throws IOException {
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

        if (DEBUG && (sourceFileInfoExtractor.getKo() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertEquals("No failures expected when analyzing " + path, 0, sourceFileInfoExtractor.getKo());
        assertEquals("No UnsupportedOperationException expected when analyzing " + path, 0, sourceFileInfoExtractor.getUnsupported());

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
            assertEquals("Line " + (i + 1) + " of " + path + " is different from what is expected", expectedLines[i].trim(), outputLines[i].trim());
        }

        assertEquals(expectedLines.length, outputLines.length);

        JavaParserFacade.clearInstances();
    }

    @Test
    public void parseUtilsUtils() throws IOException {
        parseFile("com/github/javaparser/utils/Utils");
    }

    @Test
    public void parseCommentsInserter() throws IOException {
        parseFile("com/github/javaparser/CommentsInserter");
    }

    @Test
    public void parsePositionUtils() throws IOException {
        parseFile("com/github/javaparser/utils/PositionUtils");
    }

    @Test
    public void parseModifier() throws IOException {
        parseFile("com/github/javaparser/ast/Modifier");
    }

    @Test
    public void parseNodeWithMembers() throws IOException {
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithMembers");
    }

    @Test
    public void parseAstStmts() throws IOException {
        parseFile("com/github/javaparser/ast/stmt/AssertStmt");
        parseFile("com/github/javaparser/ast/stmt/BlockStmt");
        parseFile("com/github/javaparser/ast/stmt/BreakStmt");
        parseFile("com/github/javaparser/ast/stmt/CatchClause");
        parseFile("com/github/javaparser/ast/stmt/ContinueStmt");
        parseFile("com/github/javaparser/ast/stmt/DoStmt");
        parseFile("com/github/javaparser/ast/stmt/EmptyStmt");
        parseFile("com/github/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parseFile("com/github/javaparser/ast/stmt/ExpressionStmt");
        parseFile("com/github/javaparser/ast/stmt/ForStmt");
        parseFile("com/github/javaparser/ast/stmt/ForeachStmt");
        parseFile("com/github/javaparser/ast/stmt/IfStmt");
        parseFile("com/github/javaparser/ast/stmt/LabeledStmt");
        parseFile("com/github/javaparser/ast/stmt/ReturnStmt");
        parseFile("com/github/javaparser/ast/stmt/Statement");
        parseFile("com/github/javaparser/ast/stmt/SwitchEntryStmt");
        parseFile("com/github/javaparser/ast/stmt/SwitchStmt");
        parseFile("com/github/javaparser/ast/stmt/SynchronizedStmt");
        parseFile("com/github/javaparser/ast/stmt/ThrowStmt");
        parseFile("com/github/javaparser/ast/stmt/TryStmt");
        parseFile("com/github/javaparser/ast/stmt/TypeDeclarationStmt");
        parseFile("com/github/javaparser/ast/stmt/WhileStmt");
    }

    @Test
    public void parseAstExprs() throws IOException {
        parseFile("com/github/javaparser/ast/expr/AnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/ArrayAccessExpr");
        parseFile("com/github/javaparser/ast/expr/ArrayCreationExpr");
        parseFile("com/github/javaparser/ast/expr/ArrayInitializerExpr");
        parseFile("com/github/javaparser/ast/expr/AssignExpr");
        parseFile("com/github/javaparser/ast/expr/BinaryExpr");
        parseFile("com/github/javaparser/ast/expr/BooleanLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/CastExpr");
        parseFile("com/github/javaparser/ast/expr/CharLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/ClassExpr");
        parseFile("com/github/javaparser/ast/expr/ConditionalExpr");
        parseFile("com/github/javaparser/ast/expr/DoubleLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/EnclosedExpr");
        parseFile("com/github/javaparser/ast/expr/Expression");
        parseFile("com/github/javaparser/ast/expr/FieldAccessExpr");
        parseFile("com/github/javaparser/ast/expr/InstanceOfExpr");
        parseFile("com/github/javaparser/ast/expr/IntegerLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parseFile("com/github/javaparser/ast/expr/LambdaExpr");
        parseFile("com/github/javaparser/ast/expr/LiteralExpr");
        parseFile("com/github/javaparser/ast/expr/LongLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/LongLiteralMinValueExpr");
        parseFile("com/github/javaparser/ast/expr/MarkerAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/MemberValuePair");
        parseFile("com/github/javaparser/ast/expr/MethodCallExpr");
        parseFile("com/github/javaparser/ast/expr/MethodReferenceExpr");
        parseFile("com/github/javaparser/ast/expr/NameExpr");
        parseFile("com/github/javaparser/ast/expr/NormalAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/NullLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/ObjectCreationExpr");
        parseFile("com/github/javaparser/ast/expr/QualifiedNameExpr");
        parseFile("com/github/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/StringLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/SuperExpr");
        parseFile("com/github/javaparser/ast/expr/ThisExpr");
        parseFile("com/github/javaparser/ast/expr/TypeExpr");
        parseFile("com/github/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    public void parseVariableDeclarationExpr() throws IOException {
        parseFile("com/github/javaparser/ast/expr/VariableDeclarationExpr");
    }

    @Test
    public void parseAstBody() throws IOException {
        parseFile("com/github/javaparser/ast/body/AnnotationDeclaration");
        parseFile("com/github/javaparser/ast/body/AnnotationMemberDeclaration");
        parseFile("com/github/javaparser/ast/body/BodyDeclaration");
        parseFile("com/github/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parseFile("com/github/javaparser/ast/body/ConstructorDeclaration");
        parseFile("com/github/javaparser/ast/body/EmptyMemberDeclaration");
        parseFile("com/github/javaparser/ast/body/EmptyTypeDeclaration");
        parseFile("com/github/javaparser/ast/body/EnumConstantDeclaration");
        parseFile("com/github/javaparser/ast/body/EnumDeclaration");
        parseFile("com/github/javaparser/ast/body/FieldDeclaration");
        parseFile("com/github/javaparser/ast/body/InitializerDeclaration");
        parseFile("com/github/javaparser/ast/body/MethodDeclaration");
        parseFile("com/github/javaparser/ast/body/Parameter");
        parseFile("com/github/javaparser/ast/body/TypeDeclaration");
        parseFile("com/github/javaparser/ast/body/VariableDeclarator");
        parseFile("com/github/javaparser/ast/body/VariableDeclaratorId");
    }

    @Test
    public void parseAstComments() throws IOException {
        parseFile("com/github/javaparser/ast/comments/BlockComment");
        parseFile("com/github/javaparser/ast/comments/Comment");
        parseFile("com/github/javaparser/ast/comments/CommentsCollection");
        parseFile("com/github/javaparser/ast/comments/JavadocComment");
        parseFile("com/github/javaparser/ast/comments/LineComment");
    }

    @Test
    public void parseAstCompilationUnit() throws IOException {
        parseFile("com/github/javaparser/ast/CompilationUnit");
    }

    @Test
    public void parseAstRest() throws IOException {
        parseFile("com/github/javaparser/ast/AccessSpecifier");
        parseFile("com/github/javaparser/ast/ArrayBracketPair");
        parseFile("com/github/javaparser/ast/ArrayCreationLevel");
        parseFile("com/github/javaparser/ast/Example");
        parseFile("com/github/javaparser/ast/ImportDeclaration");
        parseFile("com/github/javaparser/ast/Node");
        parseFile("com/github/javaparser/ast/PackageDeclaration");
        parseFile("com/github/javaparser/ast/UserDataKey");
    }

    @Test
    public void parseAstNodeTypes() throws IOException {
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithAnnotations");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithBlockStmt");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithBody");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithDeclaration");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithElementType");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithExtends");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithImplements");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithJavaDoc");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithModifiers");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithName");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithParameters");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithStatements");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithThrowable");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithType");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithTypeArguments");
        parseFile("com/github/javaparser/ast/nodeTypes/NodeWithVariables");
    }

    @Test
    public void parseAstTypes() throws IOException {
        parseFile("com/github/javaparser/ast/type/ArrayType");
        parseFile("com/github/javaparser/ast/type/ClassOrInterfaceType");
        parseFile("com/github/javaparser/ast/type/IntersectionType");
        parseFile("com/github/javaparser/ast/type/PrimitiveType");
        parseFile("com/github/javaparser/ast/type/ReferenceType");
        parseFile("com/github/javaparser/ast/type/Type");
        parseFile("com/github/javaparser/ast/type/TypeParameter");
        parseFile("com/github/javaparser/ast/type/UnionType");
        parseFile("com/github/javaparser/ast/type/UnknownType");
        parseFile("com/github/javaparser/ast/type/VoidType");
        parseFile("com/github/javaparser/ast/type/WildcardType");
    }

    @Test
    public void parseAstVisitor() throws IOException {
        parseFile("com/github/javaparser/ast/visitor/CloneVisitor");
        parseFile("com/github/javaparser/ast/visitor/EqualsVisitor");
        parseFile("com/github/javaparser/ast/visitor/GenericVisitor");
        parseFile("com/github/javaparser/ast/visitor/GenericVisitorAdapter");
        parseFile("com/github/javaparser/ast/visitor/ModifierVisitorAdapter");
        parseFile("com/github/javaparser/ast/visitor/TreeVisitor");
        parseFile("com/github/javaparser/ast/visitor/VoidVisitor");
        parseFile("com/github/javaparser/ast/visitor/VoidVisitorAdapter");
    }

    @Test
    public void parseDumpVisitor() throws IOException {
        parseFile("com/github/javaparser/ast/visitor/DumpVisitor");
    }

    @Test
    public void parseUtils() throws IOException {
        parseFile("com/github/javaparser/utils/ClassUtils");
        parseFile("com/github/javaparser/utils/Pair");
    }

    @Test
    public void parseAllOtherNodes() throws IOException {
        parseFile("com/github/javaparser/JavaParser");
        parseFile("com/github/javaparser/ParseProblemException");
        parseFile("com/github/javaparser/ParseResult");
        parseFile("com/github/javaparser/ParseStart");
        parseFile("com/github/javaparser/ParserConfiguration");
        parseFile("com/github/javaparser/Position");
        parseFile("com/github/javaparser/Problem");
        parseFile("com/github/javaparser/Providers");
        parseFile("com/github/javaparser/Range");
    }

}
