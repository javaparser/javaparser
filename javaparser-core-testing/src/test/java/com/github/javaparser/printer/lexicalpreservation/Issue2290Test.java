/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.stmt.ExpressionStmt;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue2290Test extends AbstractLexicalPreservingTest  {
    
    @Test
    public void test() {

        considerCode( 
                "public class Clone1 {\n" + 
                "  public static void main(String[] args) {\n" + 
                "    System.out.println(\"I'm a clone10\");\n" +
                "    System.out.println(\"I'm not a clone!\");\n" + 
                "    System.out.println(\"I'm a clone10\");\n" + 
                "  }\n" + 
                "}");
        List<ExpressionStmt> exprs = cu.findAll(ExpressionStmt.class);
        ExpressionStmt es = exprs.get(exprs.size()-1);
        es.getParentNode().get().remove(es);
        exprs = cu.findAll(ExpressionStmt.class);
        // verify that one statement is removed
        assertTrue(exprs.size()==2);
        // verify that the first statement is not removed
        assertEquals("System.out.println(\"I'm a clone10\");",exprs.get(0).toString());
    }
}
