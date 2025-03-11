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
package com.github.javaparser.ast.visitor.equals;

import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import org.junit.jupiter.api.Test;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

class EqualsVisitorPackageTest extends EqualsVisitorTest
{
    private static final String PACKAGE = "@anno package com.github.javaparser.ast.visitor.equals;";

    @Test
    void equals_samePackage_true()
    {
        parseAndClone(PACKAGE);
        boolean result = EqualsVisitor.equals(nodeLeft,nodeRight);
        assertThat(result, is(true));
    }

    @Test
    void equals_differentPackage_false()
    {
        parseAndClone(PACKAGE);
        Name packageName = nodeRight.getPackageDeclaration().get().getName();
        packageName.setIdentifier(packageName.getIdentifier()+".differentName");
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }

    @Test
    void equals_differentPackageAnnotation_false()
    {
        parseAndClone(PACKAGE);
        nodeRight.getPackageDeclaration().get().getAnnotations().remove(0);
        boolean result = EqualsVisitor.equals(nodeLeft, nodeRight);
        assertThat(result, is(false));
    }
}
