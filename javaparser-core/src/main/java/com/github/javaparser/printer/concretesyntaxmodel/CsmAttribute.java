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

package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.SourcePrinter;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

public class CsmAttribute implements CsmElement {
    public ObservableProperty getProperty() {
        return property;
    }

    private final ObservableProperty property;

    public CsmAttribute(ObservableProperty property) {
        this.property = property;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        Object value = property.getRawValue(node);
        printer.print(PrintingHelper.printToString(value));
    }

    /**
     * Obtain the token type corresponding to the specific value of the attribute.
     * For example, to the attribute "Operator" different token could correspond like PLUS or MINUS.
     *
     * @param tokenText Operator's token text
     */
    public int getTokenType(Node node, String text, String tokenText) {
        switch (property) {
            case IDENTIFIER:
                return GeneratedJavaParserConstants.IDENTIFIER;
            case TYPE: {
                String expectedImage = "\"" + text.toLowerCase() + "\"";
                for (int i=0;i<GeneratedJavaParserConstants.tokenImage.length;i++) {
                    if (GeneratedJavaParserConstants.tokenImage[i].equals(expectedImage)) {
                        return i;
                    }
                }
                throw new RuntimeException(f("Attribute '%s' does not corresponding to any expected value. Text: %s", property.camelCaseName(), text));
            }
            case KEYWORD:
            case OPERATOR: {
                String expectedImage = "\"" + tokenText.toLowerCase() + "\"";
                for (int i = 0; i < GeneratedJavaParserConstants.tokenImage.length; i++) {
                    if (GeneratedJavaParserConstants.tokenImage[i].equals(expectedImage)) {
                        return i;
                    }
                }
                throw new RuntimeException(f("Attribute '%s' does not corresponding to any expected value. Text: %s", property.camelCaseName(), tokenText));
            }
            case VALUE:
                if (node instanceof IntegerLiteralExpr) {
                    return GeneratedJavaParserConstants.INTEGER_LITERAL;
                }
            case NAME:
                return GeneratedJavaParserConstants.IDENTIFIER;
        }
        throw new UnsupportedOperationException("getTokenType does not know how to handle property "
                + property + " with text: " + text);
    }
}
