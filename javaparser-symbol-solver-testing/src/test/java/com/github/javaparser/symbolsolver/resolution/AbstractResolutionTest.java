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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;

import java.io.InputStream;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractResolutionTest extends AbstractSymbolResolutionTest {

    protected CompilationUnit parseSampleWithStandardExtension(String sampleName) {
        return parseSample(sampleName, "java");
    }

    protected CompilationUnit parseSample(String sampleName) {
        return parseSample(sampleName, "java.txt");
    }

    private CompilationUnit parseSample(String sampleName, String extension) {
        InputStream is = this.getClass().getClassLoader().getResourceAsStream(sampleName + "." + extension);
        if (is == null) {
            throw new RuntimeException("Unable to find sample " + sampleName);
        }
        return StaticJavaParser.parse(is);
    }
}
