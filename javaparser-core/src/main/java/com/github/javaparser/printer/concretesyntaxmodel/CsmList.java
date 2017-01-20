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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.printer.ConcreteSyntaxModel;
import com.github.javaparser.printer.SourcePrinter;

import java.util.Collection;
import java.util.Iterator;

public class CsmList implements CsmElement {
    private ObservableProperty property;
    private CsmElement separator;
    private CsmElement preceeding;
    private CsmElement following;

    public CsmList(ObservableProperty property, CsmElement separator) {
        this.property = property;
        this.separator = separator;
    }

    public CsmList(ObservableProperty property) {
        this.property = property;
        this.separator = null;
    }

    public CsmList(ObservableProperty property, CsmElement separator, CsmElement preceeding, CsmElement following) {
        this.property = property;
        this.separator = separator;
        this.preceeding = preceeding;
        this.following = following;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        if (property.isAboutNodes()) {
            NodeList nodeList = property.listValueFor(node);
            if (nodeList == null) {
                return;
            }
            if (!nodeList.isEmpty() && preceeding != null) {
                preceeding.prettyPrint(node, printer);
            }
            for (int i = 0; i < nodeList.size(); i++) {
                ConcreteSyntaxModel.genericPrettyPrint(nodeList.get(i), printer);
                if (separator != null && i != (nodeList.size() - 1)) {
                    separator.prettyPrint(node, printer);
                }
            }
            if (!nodeList.isEmpty() && following != null) {
                following.prettyPrint(node, printer);
            }
        } else {
            Collection<?> values = property.listPropertyFor(node);
            if (values == null) {
                return;
            }
            if (!values.isEmpty() && preceeding != null) {
                preceeding.prettyPrint(node, printer);
            }
            for (Iterator it = values.iterator(); it.hasNext(); ) {
                printer.print(it.next().toString());
                if (separator != null && it.hasNext()) {
                    separator.prettyPrint(node, printer);
                }
            }
            if (!values.isEmpty() && following != null) {
                following.prettyPrint(node, printer);
            }
        }
    }
}
