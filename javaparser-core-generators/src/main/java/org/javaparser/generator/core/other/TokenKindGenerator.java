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

package org.javaparser.generator.core.other;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.body.BodyDeclaration;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.EnumConstantDeclaration;
import org.javaparser.ast.body.EnumDeclaration;
import org.javaparser.ast.expr.IntegerLiteralExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.ast.stmt.SwitchEntry;
import org.javaparser.ast.stmt.SwitchStmt;
import org.javaparser.generator.Generator;
import org.javaparser.utils.Log;
import org.javaparser.utils.SourceRoot;

/**
 * Generates the TokenKind enum from {@link org.javaparser.GeneratedJavaParserConstants}
 */
public class TokenKindGenerator extends Generator {
    private final SourceRoot generatedJavaCcSourceRoot;

    public TokenKindGenerator(SourceRoot sourceRoot, SourceRoot generatedJavaCcSourceRoot) {
        super(sourceRoot);
        this.generatedJavaCcSourceRoot = generatedJavaCcSourceRoot;
    }

    @Override
    public void generate() {
        Log.info("Running %s", () -> getClass().getSimpleName());
        
        final CompilationUnit javaTokenCu = sourceRoot.parse("org.javaparser", "JavaToken.java");
        final ClassOrInterfaceDeclaration javaToken = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        final EnumDeclaration kindEnum = javaToken.findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind")).orElseThrow(() -> new AssertionError("Can't find class in java file."));

        kindEnum.getEntries().clear();
        annotateGenerated(kindEnum);

        final SwitchStmt valueOfSwitch = kindEnum.findFirst(SwitchStmt.class).orElseThrow(() -> new AssertionError("Can't find valueOf switch."));
        valueOfSwitch.findAll(SwitchEntry.class).stream().filter(e -> e.getLabels().isNonEmpty()).forEach(Node::remove);

        final CompilationUnit constantsCu = generatedJavaCcSourceRoot.parse("org.javaparser", "GeneratedJavaParserConstants.java");
        final ClassOrInterfaceDeclaration constants = constantsCu.getInterfaceByName("GeneratedJavaParserConstants").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        for (BodyDeclaration<?> member : constants.getMembers()) {
            member.toFieldDeclaration()
                    .filter(field -> {
                        String javadoc = field.getJavadocComment().get().getContent();
                        return javadoc.contains("RegularExpression Id") || javadoc.contains("End of File");
                    })
                    .map(field -> field.getVariable(0))
                    .ifPresent(var -> {
                        final String name = var.getNameAsString();
                        final IntegerLiteralExpr kind = var.getInitializer().get().asIntegerLiteralExpr();
                        generateEnumEntry(kindEnum, name, kind);
                        generateValueOfEntry(valueOfSwitch, name, kind);
                    });
        }
    }

    private void generateValueOfEntry(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        final SwitchEntry entry = new SwitchEntry(new NodeList<>(kind), SwitchEntry.Type.STATEMENT_GROUP, new NodeList<>(new ReturnStmt(name)));
        valueOfSwitch.getEntries().addFirst(entry);
    }

    private void generateEnumEntry(EnumDeclaration kindEnum, String name, IntegerLiteralExpr kind) {
        final EnumConstantDeclaration enumEntry = new EnumConstantDeclaration(name);
        enumEntry.getArguments().add(kind);
        kindEnum.addEntry(enumEntry);
    }
}
