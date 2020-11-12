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

package com.github.javaparser.generator.core.other;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.generator.AbstractGenerator;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

import java.util.List;

/**
 * Generates the TokenKind enum from {@link com.github.javaparser.GeneratedJavaParserConstants}
 */
public class TokenKindGenerator extends AbstractGenerator {

    private final SourceRoot generatedJavaCcSourceRoot;

    public TokenKindGenerator(SourceRoot sourceRoot, SourceRoot generatedJavaCcSourceRoot) {
        super(sourceRoot);
        this.generatedJavaCcSourceRoot = generatedJavaCcSourceRoot;
    }

    @Override
    public void generate() throws Exception {
        Log.info("Running %s", () -> getClass().getSimpleName());

        final CompilationUnit javaTokenCu = sourceRoot.parse("com.github.javaparser", "JavaToken.java");
        final ClassOrInterfaceDeclaration javaToken = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        final EnumDeclaration kindEnum = javaToken.findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind")).orElseThrow(() -> new AssertionError("Can't find class in java file."));

        List<MethodDeclaration> valueOfMethods = kindEnum.getMethodsByName("valueOf");
        if (valueOfMethods.size() != 1) {
            throw new AssertionError("Expected precisely one method named valueOf");
        }
        MethodDeclaration valueOfMethod = valueOfMethods.get(0);
        final SwitchStmt valueOfSwitch = valueOfMethod.findFirst(SwitchStmt.class).orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // TODO: Define "reset"
        // Reset the enum:
        kindEnum.getEntries().clear();
        // Reset the switch within the method valueOf(), leaving only the default
//        valueOfSwitch.getEntries().stream().filter(e -> e.getLabels().isNonEmpty()).forEach(Node::remove);

        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        SwitchEntry defaultEntry = valueOfSwitch.getDefaultSwitchEntry().get();
        valueOfSwitch.getEntries().clear();
        valueOfSwitch.getEntries().add(defaultEntry);



        // Do generation
        annotateGenerated(kindEnum);
        annotateGenerated(valueOfMethod);
        //
        final CompilationUnit constantsCu = generatedJavaCcSourceRoot.parse("com.github.javaparser", "GeneratedJavaParserConstants.java");
        final ClassOrInterfaceDeclaration constants = constantsCu.getInterfaceByName("GeneratedJavaParserConstants").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        for (BodyDeclaration<?> member : constants.getMembers()) {
            member.toFieldDeclaration()
                    .filter(field -> {
                        // TODO: Why?
                        // Only include constants that are relevant -- i.e. skip lexical state (e.g. inside comment) and literal token values.
                        String javadoc = field.getJavadocComment().get().getContent();
                        return javadoc.contains("RegularExpression Id") || javadoc.contains("End of File");
                    })
                    .map(field -> field.getVariable(0))
                    .ifPresent(var -> {
                        // For each defined constant, generate an enum and corresponding valueOf entry:
                        final String name = var.getNameAsString();
                        final IntegerLiteralExpr kind = var.getInitializer().get().asIntegerLiteralExpr();
                        generateEnumEntry(kindEnum, name, kind);
                        generateValueOfEntry(valueOfSwitch, name, kind);
                    });
        }


//        // TODO
//        // Replace with pretty printed
//        kindEnum.replace(prettyPrint(kindEnum, "        "));
//
//        valueOfMethod.replace(prettyPrint(valueOfMethod));
//        kindEnum.replace(valueOfMethod, prettyPrint(valueOfMethod));
//        valueOfSwitch.replace(prettyPrint(valueOfSwitch));
//
//        kindEnum.replace(prettyPrint(kindEnum));
//        javaTokenCu.replace(kindEnum, prettyPrint(kindEnum));

        //
        after();
    }

    private void generateEnumEntry(EnumDeclaration kindEnum, String name, IntegerLiteralExpr kind) {
        final EnumConstantDeclaration enumEntry = new EnumConstantDeclaration(name);
        enumEntry.getArguments().add(kind);
        kindEnum.addEntry(enumEntry);
    }

    private void generateValueOfEntry(SwitchStmt valueOfSwitch, String name, IntegerLiteralExpr kind) {
        final SwitchEntry entry = new SwitchEntry(new NodeList<>(kind), SwitchEntry.Type.STATEMENT_GROUP, new NodeList<>(new ReturnStmt(name)));

        // TODO: Why addFirst? Presumably to avoid adding after "default" (thus is effectively addBefore(default label).
        valueOfSwitch.getEntries().addFirst(entry);
    }
}
