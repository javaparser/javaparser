package com.github.javaparser.generator.core.other;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.generator.Generator;
import com.github.javaparser.utils.Log;
import com.github.javaparser.utils.SourceRoot;

/**
 * Generates the TokenKind enum from {@link com.github.javaparser.GeneratedJavaParserConstants}
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
        
        final CompilationUnit javaTokenCu = sourceRoot.parse("com.github.javaparser", "JavaToken.java");
        final ClassOrInterfaceDeclaration javaToken = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        final EnumDeclaration kindEnum = javaToken.findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind")).orElseThrow(() -> new AssertionError("Can't find class in java file."));

        kindEnum.getEntries().clear();
        annotateGenerated(kindEnum);

        final SwitchStmt valueOfSwitch = kindEnum.findFirst(SwitchStmt.class).orElseThrow(() -> new AssertionError("Can't find valueOf switch."));
        valueOfSwitch.findAll(SwitchEntry.class).stream().filter(e -> e.getLabels().isNonEmpty()).forEach(Node::remove);

        final CompilationUnit constantsCu = generatedJavaCcSourceRoot.parse("com.github.javaparser", "GeneratedJavaParserConstants.java");
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
