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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.AbstractTest;

import java.io.InputStream;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractResolutionTest extends AbstractTest {

    protected CompilationUnit parseSample(String sampleName) throws ParseException {
        InputStream is = this.getClass().getClassLoader().getResourceAsStream(sampleName + ".java.txt");
        if (is == null) {
            throw new RuntimeException("Unable to find sample " + sampleName);
        }
        CompilationUnit cu = JavaParser.parse(is);
        if (cu == null) {
            throw new IllegalStateException();
        }
        return cu;
    }
}
