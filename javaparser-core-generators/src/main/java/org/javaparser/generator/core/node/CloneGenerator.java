/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package org.javaparser.generator.core.node;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.generator.NodeGenerator;
import org.javaparser.metamodel.BaseNodeMetaModel;
import org.javaparser.utils.SourceRoot;

import static org.javaparser.StaticJavaParser.parseBodyDeclaration;
import static org.javaparser.utils.CodeGenerationUtils.f;

public class CloneGenerator extends NodeGenerator {
    public CloneGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        nodeCu.addImport(CloneVisitor.class);
        MethodDeclaration cloneMethod = (MethodDeclaration) parseBodyDeclaration(f(
                "@Override public %s clone() { return (%s) accept(new CloneVisitor(), null); }",
                nodeMetaModel.getTypeNameGenerified(),
                nodeMetaModel.getTypeNameGenerified()
        ));
        addOrReplaceWhenSameSignature(nodeCoid, cloneMethod);
    }
}
