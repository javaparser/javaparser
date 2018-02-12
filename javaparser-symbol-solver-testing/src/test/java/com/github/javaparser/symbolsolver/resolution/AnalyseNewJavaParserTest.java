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

import com.github.javaparser.ParseException;
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
import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * We analyze a more recent version of JavaParser, after the project moved to Java 8.
 */
@Category(SlowTest.class)
public class AnalyseNewJavaParserTest extends AbstractResolutionTest {

    private static final File src = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core"));

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"))));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        sourceFileInfoExtractor.setVerbose(true);
        return sourceFileInfoExtractor;
    }

    private static SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();

    static String readFile(File file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(Paths.get(file.getAbsolutePath()));
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parse(String fileName) throws IOException, ParseException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + fileName + ".java");
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solveMethodCalls(sourceFile);
        String output = outErrStream.toString();

        File expectedOutput = new File("src/test/resources/javaparser_methodcalls_expected_output");
        String path = adaptPath(expectedOutput).getPath() + "/" + fileName.replaceAll("/", "_") + ".txt";
        File dstFile = new File(path);

        if (isJava9()) {
            String path9 = adaptPath(expectedOutput).getPath() + "/" + fileName.replaceAll("/", "_") + "_J9.txt";
            File dstFile9 = new File(path9);
            if (dstFile9.exists()) {
                path = path9;
                dstFile = dstFile9;
            }
        }

        if (DEBUG && (sourceFileInfoExtractor.getKo() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertTrue("No failures expected when analyzing " + path, 0 == sourceFileInfoExtractor.getKo());
        assertTrue("No UnsupportedOperationException expected when analyzing " + path, 0 == sourceFileInfoExtractor.getUnsupported());

        if (!dstFile.exists()) {
            // If we need to update the file uncomment these lines
            PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
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
    public void parseUtilsUtils() throws IOException, ParseException {
        parse("com/github/javaparser/utils/Utils");
    }

    @Test
    public void parseCommentsInserter() throws IOException, ParseException {
        parse("com/github/javaparser/CommentsInserter");
    }

    @Test
    public void parsePositionUtils() throws IOException, ParseException {
        parse("com/github/javaparser/utils/PositionUtils");
    }

    @Test
    public void parseModifier() throws IOException, ParseException {
        parse("com/github/javaparser/ast/Modifier");
    }

    @Test
    public void parseNodeWithMembers() throws IOException, ParseException {
        parse("com/github/javaparser/ast/nodeTypes/NodeWithMembers");
    }

    @Test
    public void parseAstStmts() throws IOException, ParseException {
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
    public void parseAstExprs() throws IOException, ParseException {
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
    public void parseVariableDeclarationExpr() throws IOException, ParseException {
        parse("com/github/javaparser/ast/expr/VariableDeclarationExpr");
    }

    @Test
    public void parseAstBody() throws IOException, ParseException {
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
    public void parseAstComments() throws IOException, ParseException {
        parse("com/github/javaparser/ast/comments/BlockComment");
        parse("com/github/javaparser/ast/comments/Comment");
        parse("com/github/javaparser/ast/comments/CommentsCollection");
        parse("com/github/javaparser/ast/comments/JavadocComment");
        parse("com/github/javaparser/ast/comments/LineComment");
    }

    @Test
    public void parseAstRest() throws IOException, ParseException {
        parse("com/github/javaparser/ast/AccessSpecifier");
        parse("com/github/javaparser/ast/ArrayBracketPair");
        parse("com/github/javaparser/ast/ArrayCreationLevel");
        parse("com/github/javaparser/ast/CompilationUnit");
        parse("com/github/javaparser/ast/Example");
        parse("com/github/javaparser/ast/ImportDeclaration");
        parse("com/github/javaparser/ast/Node");
        parse("com/github/javaparser/ast/PackageDeclaration");
        parse("com/github/javaparser/ast/UserDataKey");
    }

    @Test
    public void parseAstNodeTypes() throws IOException, ParseException {
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
    public void parseAstTypes() throws IOException, ParseException {
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
    public void parseAstVisitor() throws IOException, ParseException {
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
    public void parseDumpVisitor() throws IOException, ParseException {
        parse("com/github/javaparser/ast/visitor/DumpVisitor");
    }

    @Test
    public void parseUtils() throws IOException, ParseException {
        parse("com/github/javaparser/utils/ClassUtils");
        parse("com/github/javaparser/utils/Pair");
    }

    @Test
    public void parseAllOtherNodes() throws IOException, ParseException {
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
