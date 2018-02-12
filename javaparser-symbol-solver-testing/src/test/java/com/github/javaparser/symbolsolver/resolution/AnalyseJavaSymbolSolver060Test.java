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
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

import org.junit.Assert;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * We analyze JavaParser version 0.6.0.
 */
@Category(SlowTest.class)
public class AnalyseJavaSymbolSolver060Test extends AbstractResolutionTest {

    private static final File root = adaptPath(new File("src/test/resources/javasymbolsolver_0_6_0"));
    private static final File src = adaptPath(new File(root + "/src"));
    private static final File lib = adaptPath(new File(root + "/lib"));
    private static final File expectedOutput = adaptPath(new File(root + "/expected_output"));

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(new File(src + "/java-symbol-solver-core")));
        combinedTypeSolver.add(new JavaParserTypeSolver(new File(src + "/java-symbol-solver-logic")));
        combinedTypeSolver.add(new JavaParserTypeSolver(new File(src + "/java-symbol-solver-model")));
        try {
			combinedTypeSolver.add(new JarTypeSolver(lib + "/guava-21.0.jar"));
			combinedTypeSolver.add(new JarTypeSolver(lib + "/javaparser-core-3.3.0.jar"));
			combinedTypeSolver.add(new JarTypeSolver(lib + "/javaslang-2.0.3.jar"));
			combinedTypeSolver.add(new JarTypeSolver(lib + "/javassist-3.19.0-GA.jar"));
		} catch (IOException e) {
			Assert.fail("one or more jar dependencies could not be found.");
			e.printStackTrace();
		}
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

    /**
     * @param projectName is one of "java-symbol-solver-core", "java-symbol-solver-logic", "java-symbol-solver-model"
     * @param fileName describes the file being analyzed
     * @throws IOException
     * @throws ParseException
     */
    private void parse(String projectName, String fileName) throws IOException, ParseException {
        File sourceFile = new File(src.getAbsolutePath() + "/" + projectName + "/" + fileName + ".java");
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solveMethodCalls(sourceFile);
        String output = outErrStream.toString();

        String path = adaptPath(expectedOutput).getPath() + "/" + projectName + "/" + fileName.replaceAll("/", "_") + ".txt";
        File dstFile = new File(path);

        if (isJava9()) {
            String path9 = adaptPath(expectedOutput).getPath() + "/" + projectName + "/" + fileName.replaceAll("/", "_") + "_J9.txt";
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
//            PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
//            writer.print(output);
//            writer.close();
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
    public void parseCoreSourceFileInfoExtractor() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/SourceFileInfoExtractor");
    }

    @Test
    public void parseCoreCoreResolution() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/core/resolution/Context");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/core/resolution/ContextHelper");
    }

    @Test
    public void parseCoreDeclarationsCommon() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/declarations/common/MethodDeclarationCommonLogic");
    }

    @Test
    public void parseCoreJavaparserNavigator() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparser/Navigator");
    }

    @Test
    public void parseCoreJavaparsermodel() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/DefaultVisitorAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/JavaParserFacade");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/JavaParserFactory");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/LambdaArgumentTypePlaceholder");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/TypeExtractor");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/UnsolvedSymbolException");
    }

    @Test
    public void parseCoreJavaparsermodelContexts() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/AbstractJavaParserContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/AbstractMethodLikeDeclarationContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/AnonymousClassDeclarationContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/CatchClauseContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/ClassOrInterfaceDeclarationContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/CompilationUnitContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/ConstructorContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/ContextHelper");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/EnumDeclarationContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/FieldAccessContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/ForechStatementContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/ForStatementContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/JavaParserTypeDeclarationAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/LambdaExprContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/MethodCallExprContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/MethodContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/StatementContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/SwitchEntryContext");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/contexts/TryWithResourceContext");
    }

    @Test
    public void parseCoreJavaparsermodelDeclarations() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/DefaultConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/Helper");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserAnnotationDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserAnonymousClassDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserClassDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserEnumConstantDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserEnumDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserFieldDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserInterfaceDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserMethodDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserParameterDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserSymbolDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeParameter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeVariableDeclaration");
    }

    @Test
    public void parseCoreJavaparsermodelDeclarators() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/AbstractSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/FieldSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/NoSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/ParameterSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/VariableSymbolDeclarator");
    }

    @Test
    public void parseCoreJavassistmodel() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistClassDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistEnumDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistFactory");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistFieldDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistInterfaceDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistMethodDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistParameterDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistTypeDeclarationAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistTypeParameter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistUtils");
    }

    @Test
    public void parseCoreModelTypesystem() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/model/typesystem/LazyType");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/model/typesystem/ReferenceTypeImpl");
    }

    @Test
    public void parseCoreReflectionmodel() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/MyObjectProvider");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionClassAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionClassDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionEnumDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionFactory");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionFieldDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionInterfaceDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionMethodDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionMethodResolutionLogic");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionParameterDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/ReflectionTypeParameter");
    }

    @Test
    public void parseCoreReflectionmodelComparators() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/ClassComparator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/MethodComparator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/ParameterComparator");
    }

    @Test
    public void parseCoreResolution() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/ConstructorResolutionLogic");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/MethodResolutionLogic");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/SymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/SymbolSolver");
    }

    @Test
    public void parseCoreResolutionTypesolvers() throws IOException, ParseException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/CombinedTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/JarTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/JavaParserTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/MemoryTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/ReflectionTypeSolver");
    }

    @Test
    public void parseLogic() throws IOException, ParseException {
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/AbstractClassDeclaration");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/AbstractTypeDeclaration");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/ConfilictingGenericTypesException");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/FunctionalInterfaceLogic");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/InferenceContext");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/InferenceVariableType");
		parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/ObjectProvider");
    }

    @Test
    public void parseModelDeclarations() throws IOException, ParseException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/AccessLevel");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/AnnotationDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/ClassDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/ConstructorDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/Declaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/EnumDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/FieldDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/HasAccessLevel");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/InterfaceDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/MethodAmbiguityException");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/MethodDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/MethodLikeDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/ParameterDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/ReferenceTypeDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/TypeDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/TypeParameterDeclaration");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/TypeParametrizable");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/declarations/ValueDeclaration");
    }

    @Test
    public void parseModelMethodsMethodUsage() throws IOException, ParseException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/methods/MethodUsage");
    }

    @Test
    public void parseModelResolution() throws IOException, ParseException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/SymbolReference");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/TypeSolver");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/UnsolvedSymbolException");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/Value");
    }

    @Test
    public void parseModelTypesystem() throws IOException, ParseException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/ArrayType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/LambdaConstraintType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/NullType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/PrimitiveType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/ReferenceType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/Type");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/TypeTransformer");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/TypeVariable");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/VoidType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/Wildcard");
    }

    @Test
    public void parseModelTypesystemParametrization() throws IOException, ParseException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParametersMap");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParameterValueProvider");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParametrized");
    }
}
