/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.GeneratedJavaParserConstants.SINGLE_LINE_COMMENT;
import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class TokenCursorTest {
    private final CompilationUnit cu = parse("package com.github.javaparser.wiki_samples;" + EOL +
            EOL +
            "public class TestFile {" + EOL +
            "    public void foo(int e) {" + EOL +
            "        /* what a nice int */" + EOL +
            "        int a = 20;" + EOL +
            "    }" + EOL +
            EOL +
            "    public void abc() {" + EOL +
            EOL +
            "    }" + EOL +
            "}" + EOL);
    private final Statement statement = cu.getClassByName("TestFile").get().getMethodsByName("foo").get(0).getBody().get().getStatements().get(0);

    @Test
    public void testAddAToDo() {
        TokenCursor cursor = statement
                .getTokenRange().get()
                .getBegin()
                // create a cursor in insert mode before this token
                .createCursor();
        cursor
                // moves the cursor to the start of the previous line
                .toStartOfLine()
                .toPreviousToken()
                .toStartOfLine()
                // go to the following EOL token
                .toEndOfLine()
                // insert an EOL token (or two, need to consider platform specific EOL's here). Cursor is moved to just after it.
                .newLine()
                // insert spaces and tabs, just like they were found at the start of the previous line. Cursor is moved to just after it.
//                .indentLikePreviousLine()
                // insert a new token.
                .insert(SINGLE_LINE_COMMENT, "// TODO 1212");
        // we have now put a line comment just above the statement.
        System.out.println(cu.getTokenRange().get().toString());
    }

    @Test
    public void testDeleteMyComment() {
        statement
                .getTokenRange().get()
                .getBegin()
                .createCursor()
                // Go backwards in the token list until we find a line comment.
                .findBackwards(t -> t.getCategory().isComment())
                // Delete it
                .deleteToken()
        // Clean up trailing whitespace
//                .deleteWhitespace()
        ;
        System.out.println(cu.getTokenRange().get().toString());
    }

    @Test
    public void testGoToEndOfLine() {
        cu.getTokenRange().ifPresent(r -> {
                    TokenCursor cursor = r.getBegin().createCursor();
                    while (cursor.valid()) {
                        cursor
                                .toEndOfLine()
                                .insert(SINGLE_LINE_COMMENT, "// hi")
                                .toEndOfLine()
                                .toNextToken();
                    }
                }
        );
        assertEquals("package com.github.javaparser.wiki_samples;// hi" + EOL +
                "// hi" + EOL +
                "public class TestFile {// hi" + EOL +
                "    public void foo(int e) {// hi" + EOL +
                "        /* what a nice int */// hi" + EOL +
                "        int a = 20;// hi" + EOL +
                "    }// hi" + EOL +
                "// hi" + EOL +
                "    public void abc() {// hi" + EOL +
                "// hi" + EOL +
                "    }// hi" + EOL +
                "}// hi" + EOL, cu.getTokenRange().map(TokenRange::toString).get());
    }
}
