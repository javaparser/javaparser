/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
package com.github.javaparser.ast.validator.language_level_validations;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.validator.*;
import com.github.javaparser.ast.validator.language_level_validations.chunks.CommonValidators;
import com.github.javaparser.ast.validator.language_level_validations.chunks.ModifierValidator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.NoBinaryIntegerLiteralsValidator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.NoUnderscoresInIntegerLiteralsValidator;

/**
 * This validator validates according to Java 1.0 syntax rules.
 */
public class Java1_0Validator extends Validators {

    final Validator modifiersWithoutStrictfpAndDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods = new ModifierValidator(false, false, false);

    final Validator noAssertKeyword = new SimpleValidator<>(AssertStmt.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("'assert' keyword is not supported.", ParserConfiguration.LanguageLevel.JAVA_1_4)));

    final Validator noInnerClasses = new SimpleValidator<>(ClassOrInterfaceDeclaration.class, n -> !n.isTopLevelType(), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("inner classes or interfaces are not supported.", ParserConfiguration.LanguageLevel.JAVA_1_1)));

    final Validator noReflection = new SimpleValidator<>(ClassExpr.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Reflection is not supported.", ParserConfiguration.LanguageLevel.JAVA_1_1)));

    final Validator noGenerics = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof NodeWithTypeArguments) {
            if (((NodeWithTypeArguments<? extends Node>) node).getTypeArguments().isPresent()) {
                reporter.report(node, new UpgradeJavaMessage("Generics are not supported.", ParserConfiguration.LanguageLevel.JAVA_5));
            }
        }
        if (node instanceof NodeWithTypeParameters) {
            if (((NodeWithTypeParameters<? extends Node>) node).getTypeParameters().isNonEmpty()) {
                reporter.report(node, new UpgradeJavaMessage("Generics are not supported.", ParserConfiguration.LanguageLevel.JAVA_5));
            }
        }
    });

    final SingleNodeTypeValidator<TryStmt> tryWithoutResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty() && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, new UpgradeJavaMessage("Try has no finally and no catch.", ParserConfiguration.LanguageLevel.JAVA_7));
        }
        if (n.getResources().isNonEmpty()) {
            reporter.report(n, new UpgradeJavaMessage("Catch with resource is not supported.", ParserConfiguration.LanguageLevel.JAVA_7));
        }
    });

    final Validator noAnnotations = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof AnnotationExpr || node instanceof AnnotationDeclaration) {
            reporter.report(node, new UpgradeJavaMessage("Annotations are not supported.", ParserConfiguration.LanguageLevel.JAVA_5));
        }
    });

    final Validator noEnums = new SimpleValidator<>(EnumDeclaration.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Enumerations are not supported.", ParserConfiguration.LanguageLevel.JAVA_5)));

    final Validator noVarargs = new SimpleValidator<>(Parameter.class, Parameter::isVarArgs, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Varargs are not supported.", ParserConfiguration.LanguageLevel.JAVA_5)));

    final Validator noForEach = new SimpleValidator<>(ForEachStmt.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("For-each loops are not supported.", ParserConfiguration.LanguageLevel.JAVA_5)));

    final Validator noStaticImports = new SimpleValidator<>(ImportDeclaration.class, ImportDeclaration::isStatic, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Static imports are not supported.", ParserConfiguration.LanguageLevel.JAVA_5)));

    final Validator onlyOneLabelInSwitchCase = new SimpleValidator<>(SwitchEntry.class, n -> n.getLabels().size() > 1, (n, reporter) -> reporter.report(n.getLabels().getParentNode().get(), new UpgradeJavaMessage("Only one label allowed in a switch-case.", ParserConfiguration.LanguageLevel.JAVA_7)));

    final Validator noYield = new SimpleValidator<>(YieldStmt.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Only labels allowed in break statements.", ParserConfiguration.LanguageLevel.JAVA_13)));

    final Validator noBinaryIntegerLiterals = new NoBinaryIntegerLiteralsValidator();

    final Validator noUnderscoresInIntegerLiterals = new NoUnderscoresInIntegerLiteralsValidator();

    final Validator noMultiCatch = new SimpleValidator<>(UnionType.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Multi-catch is not supported.", ParserConfiguration.LanguageLevel.JAVA_7)));

    final Validator noLambdas = new SimpleValidator<>(LambdaExpr.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Lambdas are not supported.", ParserConfiguration.LanguageLevel.JAVA_8)));

    final Validator noModules = new SimpleValidator<>(ModuleDeclaration.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Modules are not supported.", ParserConfiguration.LanguageLevel.JAVA_9)));

    final Validator noSwitchExpressions = new SimpleValidator<>(SwitchExpr.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Switch expressions are not supported.", ParserConfiguration.LanguageLevel.JAVA_12)));

    final Validator noPatternMatchingInstanceOf = new SimpleValidator<>(InstanceOfExpr.class, n -> n.getPattern().isPresent(), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Use of patterns with instanceof is not supported.", ParserConfiguration.LanguageLevel.JAVA_14)));

    final Validator noTextBlockLiteral = new SimpleValidator<>(TextBlockLiteralExpr.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Text Block Literals are not supported.", ParserConfiguration.LanguageLevel.JAVA_15)));

    final Validator noRecordDeclaration = new SimpleValidator<>(RecordDeclaration.class, n -> true, (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Record Declarations are not supported.", ParserConfiguration.LanguageLevel.JAVA_14)));

    final Validator noSealedClasses = new SimpleValidator<>(ClassOrInterfaceDeclaration.class, n -> n.hasModifier(Modifier.Keyword.SEALED) || n.hasModifier(Modifier.Keyword.NON_SEALED), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Sealed classes are not supported.", ParserConfiguration.LanguageLevel.JAVA_15)));

    final Validator noPermitsListInClasses = new SimpleValidator<>(ClassOrInterfaceDeclaration.class, n -> n.getPermittedTypes().isNonEmpty(), (n, reporter) -> reporter.report(n, new UpgradeJavaMessage("Permitted sub-classes are not supported.", ParserConfiguration.LanguageLevel.JAVA_17)));

    final Validator noSwitchNullDefault = new SingleNodeTypeValidator<>(SwitchEntry.class, (n, reporter) -> {
        if (n.getLabels().isNonEmpty() && n.isDefault()) {
            reporter.report(n, new UpgradeJavaMessage("Switch case null, default not supported.", ParserConfiguration.LanguageLevel.JAVA_21));
        }
    });

    final Validator noSwitchPatterns = new SingleNodeTypeValidator<>(SwitchEntry.class, (n, reporter) -> {
        if (n.getGuard().isPresent() || n.getLabels().stream().anyMatch(expr -> expr.isPatternExpr())) {
            reporter.report(n, new UpgradeJavaMessage("Switch patterns not supported.", ParserConfiguration.LanguageLevel.JAVA_21));
        }
    });

    final Validator noRecordPatterns = new TreeVisitorValidator((node, reporter) -> {
        if (node instanceof RecordPatternExpr) {
            reporter.report(node, new UpgradeJavaMessage("Record patterns are not supported.", ParserConfiguration.LanguageLevel.JAVA_21));
        }
    });

    public Java1_0Validator() {
        super(new CommonValidators());
        add(modifiersWithoutStrictfpAndDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods);
        add(noAssertKeyword);
        add(noInnerClasses);
        add(noReflection);
        add(noGenerics);
        add(tryWithoutResources);
        add(noAnnotations);
        add(noEnums);
        add(noVarargs);
        add(noForEach);
        add(noStaticImports);
        add(noYield);
        add(onlyOneLabelInSwitchCase);
        add(noBinaryIntegerLiterals);
        add(noUnderscoresInIntegerLiterals);
        add(noMultiCatch);
        add(noLambdas);
        add(noModules);
        add(noSwitchExpressions);
        add(noPatternMatchingInstanceOf);
        add(noTextBlockLiteral);
        add(noRecordDeclaration);
        add(noSealedClasses);
        add(noPermitsListInClasses);
        add(noSwitchNullDefault);
        add(noSwitchPatterns);
        add(noRecordPatterns);
    }
}
