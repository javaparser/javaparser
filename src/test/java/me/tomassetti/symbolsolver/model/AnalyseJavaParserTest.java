package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ParseException;
import me.tomassetti.symbolsolver.SourceFileInfoExtractor;
import me.tomassetti.symbolsolver.model.typesolvers.CombinedTypeSolver;
import me.tomassetti.symbolsolver.model.typesolvers.JavaParserTypeSolver;
import me.tomassetti.symbolsolver.model.typesolvers.JreTypeSolver;
import org.junit.Test;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.Assert.*;

/**
 * Created by federico on 26/08/15.
 */
public class AnalyseJavaParserTest {

    private static final File src = new File("src/test/resources/javaparser_src/proper_source");

    private SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new JreTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(new File("src/test/resources/javaparser_src/generated")));
        SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor();
        sourceFileInfoExtractor.setTypeSolver(combinedTypeSolver);
        sourceFileInfoExtractor.setPrintFileName(false);
        return sourceFileInfoExtractor;
    }

    static String readFile(File file)
            throws IOException
    {
        byte[] encoded = Files.readAllBytes(Paths.get(file.getAbsolutePath()));
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private void parse(String fileName) throws IOException, ParseException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + fileName + ".java");
        SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solve(sourceFile);
        String output = outErrStream.toString();

        assertEquals(0, sourceFileInfoExtractor.getKo());
        assertEquals(0, sourceFileInfoExtractor.getUnsupported());

        File dstFile = new File("src/test/resources/javaparser_expected_output/" + fileName.replaceAll("/", "_")+ ".txt");

        String expected = readFile(dstFile);

        String[] outputLines = output.split("\n");
        String[] expectedLines = expected.split("\n");

        for (int i=0; i<Math.min(outputLines.length, expectedLines.length); i++) {
            assertEquals(expectedLines[i], outputLines[i]);
        }

        assertEquals(expectedLines.length, outputLines.length);

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
    public void parseStatements() throws IOException, ParseException {
        parse("com/github/javaparser/ast/stmt/Statement");
        parse("com/github/javaparser/ast/stmt/CatchClause");
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
        parse("com/github/javaparser/ast/visitor/CloneVisitor");
        parse("com/github/javaparser/ast/visitor/VoidVisitorAdapter");
        parse("com/github/javaparser/ast/visitor/GenericVisitorAdapter");
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
        parse("com/github/javaparser/ast/comments/LineComment");
        parse("com/github/javaparser/ast/comments/Comment");
        // TODO fix this one
        // parse("com/github/javaparser/ast/comments/CommentsParser");
        parse("com/github/javaparser/ast/comments/JavadocComment");
        parse("com/github/javaparser/ast/comments/BlockComment");
        parse("com/github/javaparser/ast/comments/CommentsCollection");
        parse("com/github/javaparser/Position");
        parse("com/github/javaparser/SourcesHelper");
        parse("com/github/javaparser/ASTHelper");
    }

}
