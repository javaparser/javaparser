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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.Test;

import static com.github.javaparser.GeneratedJavaParserConstants.SINGLE_LINE_COMMENT;
import static com.github.javaparser.JavaParser.parse;
import static com.github.javaparser.utils.Utils.EOL;

public class TokenCursorTest {
    private final CompilationUnit cu = parse("package com.github.javaparser.wiki_samples;" + EOL +
            EOL +
            "public class TestFile {" + EOL +
            "    public void foo(int e) {" + EOL +
            "        int a = 20;" + EOL +
            "    }" + EOL +
            EOL +
            "    public void abc() {" + EOL +
            EOL +
            "    }" + EOL +
            "}" + EOL);
    private final Statement statement = cu.getClassByName("TestFile").get().getMethodsByName("foo").get(0).getBody().get().getStatements().get(0);

    @Test
    public void aaa() {
        statement
                .getTokenRange().get()
                .getBegin()
                // create a cursor in insert mode before this token
                .createCursor()
                // moves the cursor to the token that is occupying the position at (line-1, column)
                .cursorUp()
                // go to the following EOL token
                .endKey()
                // insert an EOL token (or two, need to consider platform specific EOL's here). Cursor is moved to just after it.
                .returnKey()
                // insert spaces and tabs, just like they were found at the start of the previous line. Cursor is moved to just after it.
                .indentLikePreviousLine()
                // insert a new token. Cursor is moved to just after it again.
                .insert(new JavaToken(SINGLE_LINE_COMMENT, "TODO 1212"))
                .returnKey();
        // we have now put a line comment just above the statement.
        System.out.println(cu.getTokenRange().get().toString());
    }

    @Test
    public void bbb() {
        statement
                .getTokenRange().get()
                .getBegin()
                .createCursor()
                // Go backwards in the token list until we find a line comment.
                .findBackwards(t -> t.getKind() == SINGLE_LINE_COMMENT)
                // Delete it
                .deleteToken()
                // Clean up trailing whitespace
                .deleteWhitespace();
        System.out.println(cu.getTokenRange().get().toString());
    }
}
