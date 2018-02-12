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
import com.github.javaparser.ast.comments.CommentsCollection;
import org.junit.Test;

import java.io.IOException;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class CommentsInserterTest {
    private String makeFilename(String sampleName) {
        return "com/github/javaparser/issue_samples/" + sampleName + ".java.txt";
    }

    private ParseResult<CompilationUnit> parseSample(String sampleName) throws IOException {
        Provider p = Providers.resourceProvider(
                makeFilename(sampleName));
        return new JavaParser().parse(ParseStart.COMPILATION_UNIT, p);
    }

    /**
     * Issue: "When there is a String constant "\\" compilationUnit ignores all further comments"
     */
    @Test
    public void issue290() throws IOException {
        ParseResult result = parseSample("Issue290");
        CommentsCollection cc = (CommentsCollection) result.getCommentsCollection().get();
        assertEquals(1, cc.getLineComments().size());
        assertEquals(1, cc.getJavadocComments().size());
    }

    @Test
    public void issue624() throws IOException {
        parseResource(makeFilename("Issue624"));
        // Should not fail
    }

    @Test
    public void issue200EnumConstantsWithCommentsForceVerticalAlignment() {
        CompilationUnit cu = parse("public enum X {" + EOL +
                "    /** const1 javadoc */" + EOL +
                "    BORDER_CONSTANT," + EOL +
                "    /** const2 javadoc */" + EOL +
                "    ANOTHER_CONSTANT" + EOL +
                "}");
        assertEqualsNoEol("public enum X {\n" +
                "\n" +
                "    /**\n" +
                "     * const1 javadoc\n" +
                "     */\n" +
                "    BORDER_CONSTANT,\n" +
                "    /**\n" +
                "     * const2 javadoc\n" +
                "     */\n" +
                "    ANOTHER_CONSTANT\n" +
                "}\n", cu.toString());
    }

}
