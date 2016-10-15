/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

package com.github.javaparser.ast.imports;

import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.QualifiedNameExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <p>
 * This class is a base class for classes representing import declarations. Imports are optional for the
 * {@link CompilationUnit}.
 * </p>
 * The ImportDeclaration is constructed following the syntax:<br>
 * <pre>
 * {@code
 * ImportDeclaration ::= "import" ( "static" )? }{@link NameExpr}{@code ( "." "*" )? ";"
 * }
 * </pre>
 * An EmptyImportDeclaration is simply a semicolon among the import declarations.
 * <p><a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-7.html#jls-7.5">JLS 7.5. Import Declarations</a></p>
 *
 * @author Julio Vilmar Gesser
 */
public abstract class ImportDeclaration extends Node {
    public ImportDeclaration() {
        this(Range.UNKNOWN);
    }

    public ImportDeclaration(Range range) {
        super(range);
    }

    /**
     * Factory method for import declarations.
     *
     * @param range      the range the import declaration covers. Range.UNKNOWN if not known.
     * @param name       the qualified name of the import.
     * @param isStatic   whether the import is static.
     * @param isAsterisk whether the import is on demand.
     */
    public static ImportDeclaration create(Range range, NameExpr name, boolean isStatic, boolean isAsterisk) {
        assertNotNull(range);
        assertNotNull(name);
        if (isStatic) {
            if (isAsterisk) {
                return new StaticImportOnDemandDeclaration(range, new ClassOrInterfaceType(name.getQualifiedName()));
            } else {
                if (!(name instanceof QualifiedNameExpr)) {
                    throw new IllegalArgumentException("import static name has only one identifier.");
                }
                String staticMember = name.getName();
                QualifiedNameExpr qualifiedName = (QualifiedNameExpr) name;
                String className = qualifiedName.getQualifier().getQualifiedName();
                return new SingleStaticImportDeclaration(range, new ClassOrInterfaceType(className), staticMember);
            }
        } else {
            if (isAsterisk) {
                return new TypeImportOnDemandDeclaration(range, name);
            } else {
                return new SingleTypeImportDeclaration(range, new ClassOrInterfaceType(name.getQualifiedName()));
            }
        }
    }
}
