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
import com.github.javaparser.symbolsolver.AbstractTest;
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

@Category(SlowTest.class)
public class AnalyseJavaParserTest extends AbstractTest {

    private static final File src = adaptPath(new File("src/test/test_sourcecode/javaparser_src/proper_source"));

    private SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_src/generated"))));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        return sourceFileInfoExtractor;
    }

    static String readFile(File file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(Paths.get(file.getAbsolutePath()));
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parse(String fileName) throws IOException, ParseException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + fileName + ".java");
        SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solve(sourceFile);
        String output = outErrStream.toString();

        String path = "src/test/resources/javaparser_expected_output/" + fileName.replaceAll("/", "_") + ".txt";
        File dstFile = adaptPath(new File(path));

        if (DEBUG && (sourceFileInfoExtractor.getKo() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertTrue("No failures expected when analyzing " + path, 0 == sourceFileInfoExtractor.getKo());
        assertTrue("No UnsupportedOperationException expected when analyzing " + path, 0 == sourceFileInfoExtractor.getUnsupported());

        String expected = readFile(dstFile);

        String[] outputLines = output.split("\n");
        String[] expectedLines = expected.split("\n");

        for (int i = 0; i < Math.min(outputLines.length, expectedLines.length); i++) {
            assertEquals("Line " + (i + 1) + " of " + path + " is different from what is expected", expectedLines[i].trim(), outputLines[i].trim());
        }

        assertEquals(expectedLines.length, outputLines.length);

        JavaParserFacade.clearInstances();

        // If we need to update the file uncomment these lines
        //PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
        //writer.print(output);
        //writer.close();
    }

    @Test
    public void parsePositionUtils() throws IOException, ParseException {
        parse("com/github/javaparser/PositionUtils");
    }

    @Test
    public void parseJavaParser() throws IOException, ParseException {
        parse("com/github/javaparser/JavaParser");
    }

    @Test
    public void parseStatement() throws IOException, ParseException {
        parse("com/github/javaparser/ast/stmt/Statement");
    }

    @Test
    public void parseCatchClause() throws IOException, ParseException {
        parse("com/github/javaparser/ast/stmt/CatchClause");
    }

    @Test
    public void parseStatements() throws IOException, ParseException {
        parse("com/github/javaparser/ast/stmt/LabeledStmt");
        parse("com/github/javaparser/ast/stmt/BreakStmt");
        parse("com/github/javaparser/ast/stmt/ReturnStmt");
        parse("com/github/javaparser/ast/stmt/DoStmt");
        parse("com/github/javaparser/ast/stmt/AssertStmt");
        parse("com/github/javaparser/ast/stmt/ContinueStmt");
        parse("com/github/javaparser/ast/stmt/BlockStmt");
        parse("com/github/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parse("com/github/javaparser/ast/stmt/ExpressionStmt");
        parse("com/github/javaparser/ast/stmt/EmptyStmt");
        parse("com/github/javaparser/ast/stmt/SwitchStmt");
        parse("com/github/javaparser/ast/stmt/IfStmt");
        parse("com/github/javaparser/ast/stmt/SwitchEntryStmt");
        parse("com/github/javaparser/ast/stmt/SynchronizedStmt");
        parse("com/github/javaparser/ast/stmt/ForeachStmt");
        parse("com/github/javaparser/ast/stmt/ForStmt");
        parse("com/github/javaparser/ast/stmt/WhileStmt");
        parse("com/github/javaparser/ast/stmt/ThrowStmt");
        parse("com/github/javaparser/ast/stmt/TryStmt");
        parse("com/github/javaparser/ast/stmt/TypeDeclarationStmt");
    }

    @Test
    public void parseExpressions() throws IOException, ParseException {
        parse("com/github/javaparser/ast/expr/NameExpr");
        parse("com/github/javaparser/ast/expr/FieldAccessExpr");
        parse("com/github/javaparser/ast/expr/CharLiteralExpr");
        parse("com/github/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parse("com/github/javaparser/ast/expr/IntegerLiteralExpr");
        parse("com/github/javaparser/ast/expr/ArrayCreationExpr");
        parse("com/github/javaparser/ast/expr/VariableDeclarationExpr");
        parse("com/github/javaparser/ast/expr/SuperExpr");
        parse("com/github/javaparser/ast/expr/ArrayInitializerExpr");
        parse("com/github/javaparser/ast/expr/EnclosedExpr");
        parse("com/github/javaparser/ast/expr/Expression");
        parse("com/github/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parse("com/github/javaparser/ast/expr/MethodReferenceExpr");
        parse("com/github/javaparser/ast/expr/ThisExpr");
        parse("com/github/javaparser/ast/expr/LiteralExpr");
        parse("com/github/javaparser/ast/expr/AnnotationExpr");
        parse("com/github/javaparser/ast/expr/InstanceOfExpr");
        parse("com/github/javaparser/ast/expr/LongLiteralExpr");
        parse("com/github/javaparser/ast/expr/StringLiteralExpr");
        parse("com/github/javaparser/ast/expr/NullLiteralExpr");
        parse("com/github/javaparser/ast/expr/ObjectCreationExpr");
        parse("com/github/javaparser/ast/expr/TypeExpr");
        parse("com/github/javaparser/ast/expr/DoubleLiteralExpr");
        parse("com/github/javaparser/ast/expr/LongLiteralMinValueExpr");
        parse("com/github/javaparser/ast/expr/MarkerAnnotationExpr");
        parse("com/github/javaparser/ast/expr/LambdaExpr");
        parse("com/github/javaparser/ast/expr/AssignExpr");
        parse("com/github/javaparser/ast/expr/NormalAnnotationExpr");
        parse("com/github/javaparser/ast/expr/QualifiedNameExpr");
        parse("com/github/javaparser/ast/expr/MemberValuePair");
        parse("com/github/javaparser/ast/expr/ArrayAccessExpr");
        parse("com/github/javaparser/ast/expr/ClassExpr");
        parse("com/github/javaparser/ast/expr/MethodCallExpr");
        parse("com/github/javaparser/ast/expr/ConditionalExpr");
        parse("com/github/javaparser/ast/expr/CastExpr");
        parse("com/github/javaparser/ast/expr/BooleanLiteralExpr");
        parse("com/github/javaparser/ast/expr/BinaryExpr");
        parse("com/github/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    public void parseTypes() throws IOException, ParseException {
        parse("com/github/javaparser/ast/type/ClassOrInterfaceType");
        parse("com/github/javaparser/ast/type/PrimitiveType");
        parse("com/github/javaparser/ast/type/WildcardType");
        parse("com/github/javaparser/ast/type/UnknownType");
        parse("com/github/javaparser/ast/type/ReferenceType");
        parse("com/github/javaparser/ast/type/VoidType");
        parse("com/github/javaparser/ast/type/Type");
    }

    @Test
    public void parseVisitors() throws IOException, ParseException {
        parse("com/github/javaparser/ast/visitor/EqualsVisitor");
        parse("com/github/javaparser/ast/visitor/ModifierVisitorAdapter");
        parse("com/github/javaparser/ast/visitor/DumpVisitor");
        parse("com/github/javaparser/ast/visitor/VoidVisitor");
        parse("com/github/javaparser/ast/visitor/GenericVisitor");
        parse("com/github/javaparser/ast/visitor/VoidVisitorAdapter");
        parse("com/github/javaparser/ast/visitor/GenericVisitorAdapter");
    }

    @Test
    public void parseCloneVisitor() throws IOException, ParseException {
        parse("com/github/javaparser/ast/visitor/CloneVisitor");
    }

    @Test
    public void parseSourcesHelper() throws IOException, ParseException {
        parse("com/github/javaparser/SourcesHelper");
    }

    @Test
    public void parseComments() throws IOException, ParseException {
        parse("com/github/javaparser/ast/comments/LineComment");
        parse("com/github/javaparser/ast/comments/Comment");
        parse("com/github/javaparser/ast/comments/CommentsParser");
        parse("com/github/javaparser/ast/comments/JavadocComment");
        parse("com/github/javaparser/ast/comments/BlockComment");
        parse("com/github/javaparser/ast/comments/CommentsCollection");
    }

    @Test
    public void parseTheRest() throws IOException, ParseException {
        parse("com/github/javaparser/ast/internal/Utils");
        parse("com/github/javaparser/ast/body/AnnotationMemberDeclaration");
        parse("com/github/javaparser/ast/body/EnumDeclaration");
        parse("com/github/javaparser/ast/body/Parameter");
        parse("com/github/javaparser/ast/body/EnumConstantDeclaration");
        parse("com/github/javaparser/ast/body/VariableDeclarator");
        parse("com/github/javaparser/ast/body/TypeDeclaration");
        parse("com/github/javaparser/ast/body/EmptyMemberDeclaration");
        parse("com/github/javaparser/ast/body/ModifierSet");
        parse("com/github/javaparser/ast/body/VariableDeclaratorId");
        parse("com/github/javaparser/ast/body/BaseParameter");
        parse("com/github/javaparser/ast/body/AnnotableNode");
        parse("com/github/javaparser/ast/body/AnnotationDeclaration");
        parse("com/github/javaparser/ast/body/MethodDeclaration");
        parse("com/github/javaparser/ast/body/EmptyTypeDeclaration");
        parse("com/github/javaparser/ast/body/InitializerDeclaration");
        parse("com/github/javaparser/ast/body/BodyDeclaration");
        parse("com/github/javaparser/ast/body/FieldDeclaration");
        parse("com/github/javaparser/ast/body/ConstructorDeclaration");
        parse("com/github/javaparser/ast/body/WithDeclaration");
        parse("com/github/javaparser/ast/body/MultiTypeParameter");
        parse("com/github/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parse("com/github/javaparser/ast/TreeVisitor");
        parse("com/github/javaparser/ast/PackageDeclaration");
        parse("com/github/javaparser/ast/DocumentableNode");
        parse("com/github/javaparser/ast/NamedNode");
        parse("com/github/javaparser/ast/Node");
        parse("com/github/javaparser/ast/AccessSpecifier");
        parse("com/github/javaparser/ast/CompilationUnit");
        parse("com/github/javaparser/ast/TypeParameter");
        parse("com/github/javaparser/ast/ImportDeclaration");
        parse("com/github/javaparser/Position");
        parse("com/github/javaparser/ASTHelper");
    }

}
