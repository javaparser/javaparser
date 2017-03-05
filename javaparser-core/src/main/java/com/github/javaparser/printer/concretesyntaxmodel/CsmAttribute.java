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
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.SourcePrinter;

public class CsmAttribute implements CsmElement {
    public ObservableProperty getProperty() {
        return property;
    }

    private ObservableProperty property;

    public CsmAttribute(ObservableProperty property) {
        this.property = property;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        Object value = property.getRawValue(node);
        printer.print(PrintingHelper.printToString(value));
    }

    public int getTokenType(String text) {
        if (property == ObservableProperty.IDENTIFIER) {
            return GeneratedJavaParserConstants.IDENTIFIER;
        }
        if (property == ObservableProperty.TYPE) {
            for (int i=0;i<GeneratedJavaParserConstants.tokenImage.length;i++) {
                if (GeneratedJavaParserConstants.tokenImage[i].equals("\"" + text.toLowerCase() + "\"")) {
                    return i;
                }
            }
        }
        throw new UnsupportedOperationException(property.name()+ " " + text);
    }
}
