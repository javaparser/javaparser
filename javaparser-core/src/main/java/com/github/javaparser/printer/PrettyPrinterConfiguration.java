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

package com.github.javaparser.printer;

import java.util.function.Function;

import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;

public class PrettyPrinterConfiguration {
    private boolean printComments = true;
    private boolean printJavaDoc = true;
    private boolean columnAlignParameters = false;
    private boolean columnAlignFirstMethodChain = false;
    private String indent = "    ";
    private String endOfLineCharacter = EOL;
    private Function<PrettyPrinterConfiguration, PrettyPrintVisitor> visitorFactory = PrettyPrintVisitor::new;

    public String getIndent() {
        return indent;
    }

    public PrettyPrinterConfiguration setIndent(String indent) {
        this.indent = assertNotNull(indent);
        return this;
    }

    public boolean isPrintComments() {
        return printComments;
    }

    public boolean isIgnoreComments() {
        return !printComments;
    }

    public boolean isPrintJavaDoc() {
        return printJavaDoc;
    }
    
    public boolean isColumnAlignParameters() {
        return columnAlignParameters;
    }

    public boolean isColumnAlignFirstMethodChain() {
        return columnAlignFirstMethodChain;
    }

    public PrettyPrinterConfiguration setPrintComments(boolean printComments) {
        this.printComments = printComments;
        return this;
    }

    public PrettyPrinterConfiguration setPrintJavaDoc(boolean printJavaDoc) {
        this.printJavaDoc = printJavaDoc;
        return this;
    }
    
    public PrettyPrinterConfiguration setColumnAlignParameters(boolean columnAlignParameters) {
        this.columnAlignParameters = columnAlignParameters;
        return this;
    }
    
    public PrettyPrinterConfiguration setColumnAlignFirstMethodChain(boolean columnAlignFirstMethodChain) {
        this.columnAlignFirstMethodChain = columnAlignFirstMethodChain;
        return this;
    }

    public Function<PrettyPrinterConfiguration, PrettyPrintVisitor> getVisitorFactory() {
        return visitorFactory;
    }

    public PrettyPrinterConfiguration setVisitorFactory(Function<PrettyPrinterConfiguration, PrettyPrintVisitor> visitorFactory) {
        this.visitorFactory = assertNotNull(visitorFactory);
        return this;
    }

    public String getEndOfLineCharacter() {
        return endOfLineCharacter;
    }

    public PrettyPrinterConfiguration setEndOfLineCharacter(String endOfLineCharacter) {
        this.endOfLineCharacter = assertNotNull(endOfLineCharacter);
        return this;
    }
}
