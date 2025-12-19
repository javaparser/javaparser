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
package com.github.javaparser.printer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.printer.configuration.PrettyPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import java.util.function.Function;

/**
 * Pretty printer for AST nodes.
 * This class is no longer acceptable to use because it is not sufficiently configurable and it is too tied to a specific implementation
 * <p> Use {@link Printer interface or DefaultPrettyPrinter default implementation } instead.
 * @deprecated This class could be removed in a future version. Use default DefaultPrettyPrinter.
 */
@Deprecated
public class PrettyPrinter implements ConfigurablePrinter {

    private PrinterConfiguration configuration;

    private Function<PrettyPrinterConfiguration, VoidVisitor<Void>> visitorFactory;

    public PrettyPrinter() {
        this(new PrettyPrinterConfiguration());
    }

    public PrettyPrinter(PrettyPrinterConfiguration configuration) {
        this(configuration, PrettyPrintVisitor::new);
    }

    public PrettyPrinter(
            PrettyPrinterConfiguration configuration,
            Function<PrettyPrinterConfiguration, VoidVisitor<Void>> visitorFactory) {
        this.configuration = configuration;
        this.visitorFactory = visitorFactory;
    }

    /*
     * Returns the PrettyPrinter configuration
     */
    public PrinterConfiguration getConfiguration() {
        return configuration;
    }

    /*
     * set or update the PrettyPrinter configuration
     */
    public Printer setConfiguration(PrinterConfiguration configuration) {
        if (!(configuration instanceof PrettyPrinterConfiguration))
            throw new IllegalArgumentException(
                    "PrettyPrinter must be configured with a PrettyPrinterConfiguration class");
        this.configuration = configuration;
        return this;
    }

    @Override
    public String print(Node node) {
        final VoidVisitor<Void> visitor = visitorFactory.apply((PrettyPrinterConfiguration) configuration);
        node.accept(visitor, null);
        return visitor.toString();
    }
}
