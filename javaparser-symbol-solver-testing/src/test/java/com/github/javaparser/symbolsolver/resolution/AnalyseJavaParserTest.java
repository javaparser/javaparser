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
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@Category(SlowTest.class)
public class AnalyseJavaParserTest extends AbstractTest {

    private static final Path root = adaptPath("src/test/test_sourcecode/javaparser_src");
    private static final Path properSrc = root.resolve("proper_source");

    private SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(properSrc));
        combinedTypeSolver.add(new JavaParserTypeSolver(root.resolve("generated")));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        return sourceFileInfoExtractor;
    }

    static String readFile(Path file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(file);
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    private void parseFile(String fileName) throws IOException {
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

        if (DEBUG && (sourceFileInfoExtractor.getKo() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertEquals("No failures expected when analyzing " + path, 0, sourceFileInfoExtractor.getKo());
        assertEquals("No UnsupportedOperationException expected when analyzing " + path, 0, sourceFileInfoExtractor.getUnsupported());

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
    public void parsePositionUtils() throws IOException {
        parseFile("com/github/javaparser/PositionUtils");
    }

    @Test
    public void parseJavaParser() throws IOException {
        parseFile("com/github/javaparser/JavaParser");
    }

    @Test
    public void parseStatement() throws IOException {
        parseFile("com/github/javaparser/ast/stmt/Statement");
    }

    @Test
    public void parseCatchClause() throws IOException {
        parseFile("com/github/javaparser/ast/stmt/CatchClause");
    }

    @Test
    public void parseStatements() throws IOException {
        parseFile("com/github/javaparser/ast/stmt/LabeledStmt");
        parseFile("com/github/javaparser/ast/stmt/BreakStmt");
        parseFile("com/github/javaparser/ast/stmt/ReturnStmt");
        parseFile("com/github/javaparser/ast/stmt/DoStmt");
        parseFile("com/github/javaparser/ast/stmt/AssertStmt");
        parseFile("com/github/javaparser/ast/stmt/ContinueStmt");
        parseFile("com/github/javaparser/ast/stmt/BlockStmt");
        parseFile("com/github/javaparser/ast/stmt/ExplicitConstructorInvocationStmt");
        parseFile("com/github/javaparser/ast/stmt/ExpressionStmt");
        parseFile("com/github/javaparser/ast/stmt/EmptyStmt");
        parseFile("com/github/javaparser/ast/stmt/SwitchStmt");
        parseFile("com/github/javaparser/ast/stmt/IfStmt");
        parseFile("com/github/javaparser/ast/stmt/SwitchEntryStmt");
        parseFile("com/github/javaparser/ast/stmt/SynchronizedStmt");
        parseFile("com/github/javaparser/ast/stmt/ForeachStmt");
        parseFile("com/github/javaparser/ast/stmt/ForStmt");
        parseFile("com/github/javaparser/ast/stmt/WhileStmt");
        parseFile("com/github/javaparser/ast/stmt/ThrowStmt");
        parseFile("com/github/javaparser/ast/stmt/TryStmt");
        parseFile("com/github/javaparser/ast/stmt/TypeDeclarationStmt");
    }

    @Test
    public void parseExpressions() throws IOException {
        parseFile("com/github/javaparser/ast/expr/NameExpr");
        parseFile("com/github/javaparser/ast/expr/FieldAccessExpr");
        parseFile("com/github/javaparser/ast/expr/CharLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/IntegerLiteralMinValueExpr");
        parseFile("com/github/javaparser/ast/expr/IntegerLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/ArrayCreationExpr");
        parseFile("com/github/javaparser/ast/expr/VariableDeclarationExpr");
        parseFile("com/github/javaparser/ast/expr/SuperExpr");
        parseFile("com/github/javaparser/ast/expr/ArrayInitializerExpr");
        parseFile("com/github/javaparser/ast/expr/EnclosedExpr");
        parseFile("com/github/javaparser/ast/expr/Expression");
        parseFile("com/github/javaparser/ast/expr/SingleMemberAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/MethodReferenceExpr");
        parseFile("com/github/javaparser/ast/expr/ThisExpr");
        parseFile("com/github/javaparser/ast/expr/LiteralExpr");
        parseFile("com/github/javaparser/ast/expr/AnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/InstanceOfExpr");
        parseFile("com/github/javaparser/ast/expr/LongLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/StringLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/NullLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/ObjectCreationExpr");
        parseFile("com/github/javaparser/ast/expr/TypeExpr");
        parseFile("com/github/javaparser/ast/expr/DoubleLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/LongLiteralMinValueExpr");
        parseFile("com/github/javaparser/ast/expr/MarkerAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/LambdaExpr");
        parseFile("com/github/javaparser/ast/expr/AssignExpr");
        parseFile("com/github/javaparser/ast/expr/NormalAnnotationExpr");
        parseFile("com/github/javaparser/ast/expr/QualifiedNameExpr");
        parseFile("com/github/javaparser/ast/expr/MemberValuePair");
        parseFile("com/github/javaparser/ast/expr/ArrayAccessExpr");
        parseFile("com/github/javaparser/ast/expr/ClassExpr");
        parseFile("com/github/javaparser/ast/expr/MethodCallExpr");
        parseFile("com/github/javaparser/ast/expr/ConditionalExpr");
        parseFile("com/github/javaparser/ast/expr/CastExpr");
        parseFile("com/github/javaparser/ast/expr/BooleanLiteralExpr");
        parseFile("com/github/javaparser/ast/expr/BinaryExpr");
        parseFile("com/github/javaparser/ast/expr/UnaryExpr");
    }

    @Test
    public void parseTypes() throws IOException {
        parseFile("com/github/javaparser/ast/type/ClassOrInterfaceType");
        parseFile("com/github/javaparser/ast/type/PrimitiveType");
        parseFile("com/github/javaparser/ast/type/WildcardType");
        parseFile("com/github/javaparser/ast/type/UnknownType");
        parseFile("com/github/javaparser/ast/type/ReferenceType");
        parseFile("com/github/javaparser/ast/type/VoidType");
        parseFile("com/github/javaparser/ast/type/Type");
    }

    @Test
    public void parseVisitors() throws IOException {
        parseFile("com/github/javaparser/ast/visitor/EqualsVisitor");
        parseFile("com/github/javaparser/ast/visitor/ModifierVisitorAdapter");
        parseFile("com/github/javaparser/ast/visitor/DumpVisitor");
        parseFile("com/github/javaparser/ast/visitor/VoidVisitor");
        parseFile("com/github/javaparser/ast/visitor/GenericVisitor");
        parseFile("com/github/javaparser/ast/visitor/VoidVisitorAdapter");
        parseFile("com/github/javaparser/ast/visitor/GenericVisitorAdapter");
    }

    @Test
    public void parseCloneVisitor() throws IOException {
        parseFile("com/github/javaparser/ast/visitor/CloneVisitor");
    }

    @Test
    public void parseSourcesHelper() throws IOException {
        parseFile("com/github/javaparser/SourcesHelper");
    }

    @Test
    public void parseComments() throws IOException {
        parseFile("com/github/javaparser/ast/comments/LineComment");
        parseFile("com/github/javaparser/ast/comments/Comment");
        parseFile("com/github/javaparser/ast/comments/CommentsParser");
        parseFile("com/github/javaparser/ast/comments/JavadocComment");
        parseFile("com/github/javaparser/ast/comments/BlockComment");
        parseFile("com/github/javaparser/ast/comments/CommentsCollection");
    }

    @Test
    public void parseTheRest() throws IOException {
        parseFile("com/github/javaparser/ast/internal/Utils");
        parseFile("com/github/javaparser/ast/body/AnnotationMemberDeclaration");
        parseFile("com/github/javaparser/ast/body/EnumDeclaration");
        parseFile("com/github/javaparser/ast/body/Parameter");
        parseFile("com/github/javaparser/ast/body/EnumConstantDeclaration");
        parseFile("com/github/javaparser/ast/body/VariableDeclarator");
        parseFile("com/github/javaparser/ast/body/TypeDeclaration");
        parseFile("com/github/javaparser/ast/body/EmptyMemberDeclaration");
        parseFile("com/github/javaparser/ast/body/ModifierSet");
        parseFile("com/github/javaparser/ast/body/VariableDeclaratorId");
        parseFile("com/github/javaparser/ast/body/BaseParameter");
        parseFile("com/github/javaparser/ast/body/AnnotableNode");
        parseFile("com/github/javaparser/ast/body/AnnotationDeclaration");
        parseFile("com/github/javaparser/ast/body/MethodDeclaration");
        parseFile("com/github/javaparser/ast/body/EmptyTypeDeclaration");
        parseFile("com/github/javaparser/ast/body/InitializerDeclaration");
        parseFile("com/github/javaparser/ast/body/BodyDeclaration");
        parseFile("com/github/javaparser/ast/body/FieldDeclaration");
        parseFile("com/github/javaparser/ast/body/ConstructorDeclaration");
        parseFile("com/github/javaparser/ast/body/WithDeclaration");
        parseFile("com/github/javaparser/ast/body/MultiTypeParameter");
        parseFile("com/github/javaparser/ast/body/ClassOrInterfaceDeclaration");
        parseFile("com/github/javaparser/ast/TreeVisitor");
        parseFile("com/github/javaparser/ast/PackageDeclaration");
        parseFile("com/github/javaparser/ast/DocumentableNode");
        parseFile("com/github/javaparser/ast/NamedNode");
        parseFile("com/github/javaparser/ast/Node");
        parseFile("com/github/javaparser/ast/AccessSpecifier");
        parseFile("com/github/javaparser/ast/CompilationUnit");
        parseFile("com/github/javaparser/ast/TypeParameter");
        parseFile("com/github/javaparser/ast/ImportDeclaration");
        parseFile("com/github/javaparser/Position");
        parseFile("com/github/javaparser/ASTHelper");
    }

}
