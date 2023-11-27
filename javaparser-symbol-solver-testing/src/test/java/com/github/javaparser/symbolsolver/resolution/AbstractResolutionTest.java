/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.resolution.TypeSolver;
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

    protected CompilationUnit parseSampleWithStandardExtension(String sampleName, TypeSolver typeSolver) {
        return parseSample(sampleName, "java", typeSolver);
    }

    protected CompilationUnit parseSample(String sampleName, TypeSolver typeSolver) {
        return parseSample(sampleName, "java.txt", typeSolver);
    }

    private CompilationUnit parseSample(String sampleName, String extension, TypeSolver typeSolver) {
        InputStream is = this.getClass().getClassLoader().getResourceAsStream(sampleName + "." + extension);
        if (is == null) {
            throw new RuntimeException("Unable to find sample " + sampleName);
        }
        JavaParser javaParser = createParserWithResolver(typeSolver);
        return javaParser.parse(is).getResult().orElseThrow(() -> new IllegalArgumentException("Sample does not parse: " + sampleName));
    }

    protected JavaParser createParserWithResolver(TypeSolver typeSolver) {
        return new JavaParser(new ParserConfiguration().setSymbolResolver(symbolResolver(typeSolver)));
    }
    
}
