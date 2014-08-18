/*
 * Copyright (C) 2014, The GitHub project https://github.com/matozoid/javaparser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
package japa.parser.ast;

import japa.parser.ast.CompilationUnit;
import japa.parser.ast.Node;
import org.junit.Test;
import static org.junit.Assert.*;

/**
 * @author Federico Tomassetti
 * @since July 2014
 */
public class TestNode {

    @Test public void testIssue52NodeEqualsWorkWithNull() throws Exception {
        Node n = new CompilationUnit();
        assertFalse(n.equals(null));
    }

    @Test public void testIssue52NodeEqualsWorkWithArbitraryObjects() throws Exception {
        Node n = new CompilationUnit();
        assertFalse(n.equals("anObjectWhichIsNotANode, it is a String"));
    }

}
