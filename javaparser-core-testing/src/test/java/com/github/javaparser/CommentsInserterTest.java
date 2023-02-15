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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static com.github.javaparser.utils.TestUtils.assertEqualToTextResourceNoEol;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class CommentsInserterTest {
    private String makeFilename(String sampleName) {
        return "com/github/javaparser/issue_samples/" + sampleName + ".java.txt";
    }

    private String makeExpectedFilename(String sampleName) {
        return "/com/github/javaparser/issue_samples/" + sampleName + ".java.expected.txt";
    }

    private ParseResult<CompilationUnit> parseSample(String sampleName) throws IOException {
        Provider p = Providers.resourceProvider(makeFilename(sampleName));
        return new JavaParser().parse(ParseStart.COMPILATION_UNIT, p);
    }

    /**
     * Issue: "When there is a String constant "\\" compilationUnit ignores all further comments"
     */
    @Test
    void issue290() throws IOException {
        ParseResult<CompilationUnit> result = this.parseSample("Issue290");
        CommentsCollection cc = result.getCommentsCollection().get();
        assertEquals(1, cc.getLineComments().size());
        assertEquals(1, cc.getJavadocComments().size());
    }

    @Test
    void issue624() throws IOException {
        this.parseSample("Issue624");
        // Should not fail
    }

    @Test
    void issue200EnumConstantsWithCommentsForceVerticalAlignment() {
        CompilationUnit cu = TestParser.parseCompilationUnit("public enum X {" + SYSTEM_EOL +
                "    /** const1 javadoc */" + SYSTEM_EOL +
                "    BORDER_CONSTANT," + SYSTEM_EOL +
                "    /** const2 javadoc */" + SYSTEM_EOL +
                "    ANOTHER_CONSTANT" + SYSTEM_EOL +
                "}");
        assertEqualsStringIgnoringEol("public enum X {\n" +
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

    @Test
    void issue234LosingCommentsInArrayInitializerExpr() {
        CompilationUnit cu = TestParser.parseCompilationUnit("@Anno(stuff={" + SYSTEM_EOL +
                "    // Just," + SYSTEM_EOL +
                "    // an," + SYSTEM_EOL +
                "    // example" + SYSTEM_EOL +
                "})" + SYSTEM_EOL +
                "class ABC {" + SYSTEM_EOL +
                "" + SYSTEM_EOL +
                "}");

        assertEqualsStringIgnoringEol("@Anno(stuff = {// Just,\n" +
                "// an,\n" +
                "// example\n" +
                "})\n" +
                "class ABC {\n" +
                "}\n", cu.toString());
    }


    @Test
    void issue412() throws IOException {
        CompilationUnit cu = parseSample("Issue412").getResult().get();
        assertEqualToTextResourceNoEol(makeExpectedFilename("Issue412"), cu.toString());
    }
}
