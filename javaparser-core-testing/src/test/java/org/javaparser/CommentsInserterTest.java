/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package org.javaparser;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.comments.CommentsCollection;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.javaparser.StaticJavaParser.parse;
import static org.javaparser.StaticJavaParser.parseResource;
import static org.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class CommentsInserterTest {
    private String makeFilename(String sampleName) {
        return "org/javaparser/issue_samples/" + sampleName + ".java.txt";
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
    void issue290() throws IOException {
        ParseResult result = parseSample("Issue290");
        CommentsCollection cc = (CommentsCollection) result.getCommentsCollection().get();
        assertEquals(1, cc.getLineComments().size());
        assertEquals(1, cc.getJavadocComments().size());
    }

    @Test
    void issue624() throws IOException {
        parseResource(makeFilename("Issue624"));
        // Should not fail
    }

    @Test
    void issue200EnumConstantsWithCommentsForceVerticalAlignment() {
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

    @Test
    void issue234LosingCommentsInArrayInitializerExpr() {
        CompilationUnit cu = parse("@Anno(stuff={" + EOL +
                "    // Just," + EOL +
                "    // an," + EOL +
                "    // example" + EOL +
                "})" + EOL +
                "class ABC {" + EOL +
                "" + EOL +
                "}");

        assertEqualsNoEol("@Anno(stuff = {// Just,\n" +
                "// an,\n" +
                "// example\n" +
                "})\n" +
                "class ABC {\n" +
                "}\n", cu.toString());
    }

}
