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
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * We analyze JavaParser version 0.6.0.
 */
@SlowTest
class AnalyseJavaSymbolSolver060Test extends AbstractResolutionTest {

    private static final Path root = adaptPath("src/test/test_sourcecode/javasymbolsolver_0_6_0");
    private static final Path src = root.resolve("src");
    private static final Path lib = root.resolve("lib");
    private static final Path expectedOutput = root.resolve("expected_output");

    private static SourceFileInfoExtractor getSourceFileInfoExtractor() {
        try {
            CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(
                    new ReflectionTypeSolver(),
                    new JavaParserTypeSolver(new File(src + "/java-symbol-solver-core")),
                    new JavaParserTypeSolver(new File(src + "/java-symbol-solver-logic")),
                    new JavaParserTypeSolver(new File(src + "/java-symbol-solver-model")),
                    new JarTypeSolver(lib + "/guava-21.0.jar"),
                    new JarTypeSolver(lib + "/javaparser-core-3.3.0.jar"),
                    new JarTypeSolver(lib + "/javaslang-2.0.3.jar"),
                    new JarTypeSolver(lib + "/javassist-3.19.0-GA.jar"));
            SourceFileInfoExtractor sourceFileInfoExtractor = new SourceFileInfoExtractor(combinedTypeSolver);
            sourceFileInfoExtractor.setPrintFileName(false);
            sourceFileInfoExtractor.setVerbose(true);
            return sourceFileInfoExtractor;
        } catch (IOException e) {
            fail("one or more jar dependencies could not be found.");
            return null;
        }
    }

    private static SourceFileInfoExtractor sourceFileInfoExtractor = getSourceFileInfoExtractor();

    private static String readFile(File file)
            throws IOException {
        byte[] encoded = Files.readAllBytes(Paths.get(file.getAbsolutePath()));
        return new String(encoded, StandardCharsets.UTF_8);
    }

    private static final boolean DEBUG = true;

    /**
     * @param projectName is one of "java-symbol-solver-core", "java-symbol-solver-logic", "java-symbol-solver-model"
     * @param fileName describes the file being analyzed
     */
    private void parse(String projectName, String fileName) throws IOException {
        Path sourceFile = src.resolve(projectName + "/" + fileName + ".java");
        OutputStream outErrStream = new ByteArrayOutputStream();
        PrintStream outErr = new PrintStream(outErrStream);

        sourceFileInfoExtractor.setOut(outErr);
        sourceFileInfoExtractor.setErr(outErr);
        sourceFileInfoExtractor.solveMethodCalls(sourceFile);
        String output = outErrStream.toString();

        String path = adaptPath(expectedOutput) + "/" + projectName + "/" + fileName.replaceAll("/", "_") + ".txt";
        File dstFile = new File(path);  

        if (isJavaVersion9OrAbove()) {
            String path9 = adaptPath(expectedOutput) + "/" + projectName + "/" + fileName.replaceAll("/", "_") + "_J9.txt";
            File dstFile9 = new File(path9);
            if (dstFile9.exists()) {
                path = path9;
                dstFile = dstFile9;
            }
        }

        if (DEBUG && (sourceFileInfoExtractor.getFailures() != 0 || sourceFileInfoExtractor.getUnsupported() != 0)) {
            System.err.println(output);
        }

        assertEquals(0, sourceFileInfoExtractor.getFailures(), "No failures expected when analyzing " + path);
        assertEquals(0, sourceFileInfoExtractor.getUnsupported(), "No UnsupportedOperationException expected when analyzing " + path);

        // If we need to update the file uncomment these lines
//        if (!dstFile.exists()) {
//            PrintWriter writer = new PrintWriter(dstFile.getAbsoluteFile(), "UTF-8");
//            writer.print(output);
//            writer.close();
//        }

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
    void parseCoreSourceFileInfoExtractor() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/SourceFileInfoExtractor");
    }

    @Test
    void parseCoreCoreResolution() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/core/resolution/Context");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/core/resolution/ContextHelper");
    }

    @Test
    void parseCoreDeclarationsCommon() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/declarations/common/MethodDeclarationCommonLogic");
    }

    @Test
    void parseCoreJavaparserNavigator() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparser/Navigator");
    }

    @Test
    void parseCoreJavaparsermodelTypeExtractor() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/TypeExtractor");
    }

    @Test
    void parseCoreJavaparsermodel() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/DefaultVisitorAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/JavaParserFacade");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/JavaParserFactory");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/LambdaArgumentTypePlaceholder");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/UnsolvedSymbolException");
    }

    @Test
    void parseCoreJavaparsermodelContexts() throws IOException {
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
    void parseCoreJavaparsermodelJavaParserAnonymousClassDeclaration() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserAnonymousClassDeclaration");
    }

    @Test
    void parseCoreJavaparsermodelJavaParserInterfaceDeclaration() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserInterfaceDeclaration");
    }

    @Test
    void parseCoreJavaparsermodelDeclarationsHelper() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/Helper");
    }

    @Test
    void parseCoreJavaparsermodelDeclarationsJavaParserFieldDeclaration() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserFieldDeclaration");
    }

    @Test
    void parseCoreJavaparsermodelDeclarations() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/DefaultConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserAnnotationDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserClassDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserConstructorDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserEnumConstantDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserEnumDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserMethodDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserParameterDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserSymbolDeclaration");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeAdapter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeParameter");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarations/JavaParserTypeVariableDeclaration");
    }

    @Test
    void parseCoreJavaparsermodelDeclarators() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/AbstractSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/FieldSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/NoSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/ParameterSymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javaparsermodel/declarators/VariableSymbolDeclarator");
    }

    @Test
    void parseCoreJavassistmodelJavassistClassDeclaration() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/javassistmodel/JavassistClassDeclaration");
    }

    @Test
    void parseCoreJavassistmodel() throws IOException {
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
    void parseCoreModelTypesystem() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/model/typesystem/LazyType");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/model/typesystem/ReferenceTypeImpl");
    }

    @Test
    void parseCoreReflectionmodel() throws IOException {
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
    void parseCoreReflectionmodelComparators() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/ClassComparator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/MethodComparator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/reflectionmodel/comparators/ParameterComparator");
    }

    @Test
    void parseCoreResolution() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/ConstructorResolutionLogic");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/MethodResolutionLogic");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/SymbolDeclarator");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/SymbolSolver");
    }

    @Test
    void parseCoreResolutionTypesolvers() throws IOException {
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/CombinedTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/JarTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/JavaParserTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/MemoryTypeSolver");
        parse("java-symbol-solver-core", "com/github/javaparser/symbolsolver/resolution/typesolvers/ReflectionTypeSolver");
    }

    @Test
    void parseLogic() throws IOException {
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/AbstractClassDeclaration");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/AbstractTypeDeclaration");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/ConfilictingGenericTypesException");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/FunctionalInterfaceLogic");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/InferenceContext");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/InferenceVariableType");
        parse("java-symbol-solver-logic", "com/github/javaparser/symbolsolver/logic/ObjectProvider");
    }

    @Test
    void parseModelDeclarations() throws IOException {
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
    void parseModelMethodsMethodUsage() throws IOException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/methods/MethodUsage");
    }

    @Test
    void parseModelResolution() throws IOException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/SymbolReference");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/TypeSolver");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/UnsolvedSymbolException");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/resolution/Value");
    }

    @Test
    void parseModelTypesystemReferenceType() throws IOException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/ReferenceType");
    }

    @Test
    void parseModelTypesystem() throws IOException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/ArrayType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/LambdaConstraintType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/NullType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/PrimitiveType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/Type");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/TypeTransformer");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/TypeVariable");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/VoidType");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/Wildcard");
    }

    @Test
    void parseModelTypesystemParametrization() throws IOException {
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParametersMap");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParameterValueProvider");
        parse("java-symbol-solver-model", "com/github/javaparser/symbolsolver/model/typesystem/parametrization/TypeParametrized");
    }
}
