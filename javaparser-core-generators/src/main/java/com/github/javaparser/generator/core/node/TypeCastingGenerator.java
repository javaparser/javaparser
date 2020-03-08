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

package com.github.javaparser.generator.core.node;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.generator.NodeGenerator;
import com.github.javaparser.metamodel.BaseNodeMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.utils.Pair;
import com.github.javaparser.utils.SourceRoot;

import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.set;

public class TypeCastingGenerator extends NodeGenerator {

    private final Set<BaseNodeMetaModel> baseNodes;

    public TypeCastingGenerator(SourceRoot sourceRoot) {
        super(sourceRoot);
        this.baseNodes = set(
                JavaParserMetaModel.statementMetaModel,
                JavaParserMetaModel.expressionMetaModel,
                JavaParserMetaModel.typeMetaModel,
                JavaParserMetaModel.moduleDirectiveMetaModel,
                JavaParserMetaModel.bodyDeclarationMetaModel,
                JavaParserMetaModel.commentMetaModel
        );
    }

    @Override
    protected void generateNode(BaseNodeMetaModel nodeMetaModel, CompilationUnit nodeCu, ClassOrInterfaceDeclaration nodeCoid) {
        Pair<CompilationUnit, ClassOrInterfaceDeclaration> baseCode = null;


        for (BaseNodeMetaModel baseNode : this.baseNodes) {
            if (nodeMetaModel == baseNode) {
                // We adjust the base models from the child nodes, so do not do anything when we *are* the base model.
                return;
            }
            if (nodeMetaModel.isInstanceOfMetaModel(baseNode)) {
                baseCode = this.parseNode(baseNode);
            }
        }

        if (baseCode == null) {
            // Node is not a child of one of the base nodes, so we don't want to generate this method for it.
            return;
        }

        final String typeName = nodeMetaModel.getTypeName();
        final ClassOrInterfaceDeclaration baseCoid = baseCode.b;
        final CompilationUnit baseCu = baseCode.a;

        this.generateIsType(baseCu, nodeCoid, baseCoid, typeName);
        this.generateAsType(baseCu, nodeCoid, baseCoid, typeName);
        this.generateToType(nodeCu, baseCu, nodeCoid, baseCoid, typeName);
        this.generateIfType(nodeCu, baseCu, nodeCoid, baseCoid, typeName);
    }


    private void generateIsType(CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        final MethodDeclaration baseIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("public boolean is%s() { return false; }", typeName));
        final MethodDeclaration overriddenIsTypeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public boolean is%s() { return true; }", typeName));

        this.addOrReplaceWhenSameSignature(nodeCoid, overriddenIsTypeMethod);
        this.addOrReplaceWhenSameSignature(baseCoid, baseIsTypeMethod);
    }

    private void generateAsType(CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        baseCu.addImport("com.github.javaparser.utils.CodeGenerationUtils.f", true, false);

        final MethodDeclaration asTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public %s as%s() { throw new IllegalStateException(f(\"%%s is not an %s\", this)); }", typeName, typeName, typeName));
        final MethodDeclaration asTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public %s as%s() { return this; }", typeName, typeName));

        this.addOrReplaceWhenSameSignature(baseCoid, asTypeBaseMethod);
        this.addOrReplaceWhenSameSignature(nodeCoid, asTypeNodeMethod);
    }

    private void generateToType(CompilationUnit nodeCu, CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        baseCu.addImport(Optional.class);
        nodeCu.addImport(Optional.class);

        final MethodDeclaration asTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public Optional<%s> to%s() { return Optional.empty(); }", typeName, typeName, typeName));
        final MethodDeclaration asTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public Optional<%s> to%s() { return Optional.of(this); }", typeName, typeName));

        this.addOrReplaceWhenSameSignature(baseCoid, asTypeBaseMethod);
        this.addOrReplaceWhenSameSignature(nodeCoid, asTypeNodeMethod);
    }

    private void generateIfType(CompilationUnit nodeCu, CompilationUnit baseCu, ClassOrInterfaceDeclaration nodeCoid, ClassOrInterfaceDeclaration baseCoid, String typeName) {
        baseCu.addImport(Consumer.class);
        nodeCu.addImport(Consumer.class);

        final MethodDeclaration ifTypeBaseMethod = (MethodDeclaration) parseBodyDeclaration(f("public void if%s(Consumer<%s> action) { }", typeName, typeName));
        final MethodDeclaration ifTypeNodeMethod = (MethodDeclaration) parseBodyDeclaration(f("@Override public void if%s(Consumer<%s> action) { action.accept(this); }", typeName, typeName));

        this.addOrReplaceWhenSameSignature(baseCoid, ifTypeBaseMethod);
        this.addOrReplaceWhenSameSignature(nodeCoid, ifTypeNodeMethod);
    }

    @Override
    public String toString() {
        return "TypeCastingGenerator{" +
                "baseNodes=" + this.baseNodes +
                ", sourceRoot=" + this.sourceRoot +
                '}';
    }
}
