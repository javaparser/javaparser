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

import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.JavadocBlockTag;
import com.github.javaparser.javadoc.description.JavadocDescription;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;

class JavadocParserTest {

    @Test
    void parseSimplestContent() {
        Assertions.assertEquals(new Javadoc(JavadocDescription.parseText("A simple line of text")),
                JavadocParser.parse("A simple line of text"));
    }

    @Test
    void parseEmptySingleLine() {
        Assertions.assertEquals(new Javadoc(JavadocDescription.parseText("")),
                JavadocParser.parse(SYSTEM_EOL));
    }

    @Test
    void parseSingleLineWithSpacing() {
        assertEquals(new Javadoc(JavadocDescription.parseText("The line number of the first character of this Token.")),
                JavadocParser.parse(" The line number of the first character of this Token. "));
    }

    @Test
    void parseSingleLineWithNewLines() {
        assertEquals(new Javadoc(JavadocDescription.parseText("The string image of the token.")),
                JavadocParser.parse(SYSTEM_EOL +
                        "   * The string image of the token." + SYSTEM_EOL +
                        "   "));
    }

    @Test
    void parseCommentWithNewLines() {
        String text = SYSTEM_EOL +
                "   * The version identifier for this Serializable class." + SYSTEM_EOL +
                "   * Increment only if the <i>serialized</i> form of the" + SYSTEM_EOL +
                "   * class changes." + SYSTEM_EOL +
                "   ";
        assertEquals(new Javadoc(JavadocDescription.parseText("The version identifier for this Serializable class." + SYSTEM_EOL +
                        "Increment only if the <i>serialized</i> form of the" + SYSTEM_EOL +
                        "class changes.")),
                JavadocParser.parse(text));
    }

    @Test
    void parseCommentWithIndentation() {
        String text = "Returns a new Token object, by default." + SYSTEM_EOL +
                "   * However, if you want, you can create and return subclass objects based on the value of ofKind." + SYSTEM_EOL +
                "   *" + SYSTEM_EOL +
                "   *    case MyParserConstants.ID : return new IDToken(ofKind, image);" + SYSTEM_EOL +
                "   *" + SYSTEM_EOL +
                "   * to the following switch statement. Then you can cast matchedToken";
        assertEquals(new Javadoc(JavadocDescription.parseText("Returns a new Token object, by default." + SYSTEM_EOL +
                        "However, if you want, you can create and return subclass objects based on the value of ofKind." + SYSTEM_EOL +
                        SYSTEM_EOL +
                        "   case MyParserConstants.ID : return new IDToken(ofKind, image);" + SYSTEM_EOL +
                        SYSTEM_EOL +
                        "to the following switch statement. Then you can cast matchedToken")),
                JavadocParser.parse(text));
    }

    @Test
    void parseBlockTagsAndEmptyDescription() {
        String text = SYSTEM_EOL +
                "   * @deprecated" + SYSTEM_EOL +
                "   * @see #getEndColumn" + SYSTEM_EOL +
                "   ";
        assertEquals(new Javadoc(JavadocDescription.parseText(""))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.DEPRECATED, ""))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.SEE, "#getEndColumn")), JavadocParser.parse(text));
    }

    @Test
    void parseBlockTagsAndProvideTagName() {
        String expectedText = SYSTEM_EOL +
                "   * @unofficial" + SYSTEM_EOL + " " +
                "   ";

        Javadoc underTest = new Javadoc(JavadocDescription.parseText(""))
                .addBlockTag(new JavadocBlockTag("unofficial", ""));


        assertEquals(underTest, JavadocParser.parse(expectedText));
        assertEquals(1, underTest.getBlockTags().size());
        assertEquals("unofficial", underTest.getBlockTags().get(0).getTagName());
    }

    @Test
    void parseParamBlockTags() {
        String text = SYSTEM_EOL +
                "     * Add a field to this and automatically add the import of the type if needed" + SYSTEM_EOL +
                "     *" + SYSTEM_EOL +
                "     * @param typeClass the type of the field" + SYSTEM_EOL +
                "     *       @param name the name of the field" + SYSTEM_EOL +
                "     * @param modifiers the modifiers like {@link Modifier#PUBLIC}" + SYSTEM_EOL +
                "     * @return the {@link FieldDeclaration} created" + SYSTEM_EOL +
                "     ";
        Javadoc res = JavadocParser.parse(text);
        assertEquals(new Javadoc(JavadocDescription.parseText("Add a field to this and automatically add the import of the type if needed"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("typeClass", "the type of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("name", "the name of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("modifiers", "the modifiers like {@link Modifier#PUBLIC}"))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.RETURN, "the {@link FieldDeclaration} created")), res);
    }

    @Test
    void parseMultilineParamBlockTags() {
        String text = SYSTEM_EOL +
                "     * Add a field to this and automatically add the import of the type if needed" + SYSTEM_EOL +
                "     *" + SYSTEM_EOL +
                "     * @param typeClass the type of the field" + SYSTEM_EOL +
                "     *     continued in a second line" + SYSTEM_EOL +
                "     * @param name the name of the field" + SYSTEM_EOL +
                "     * @param modifiers the modifiers like {@link Modifier#PUBLIC}" + SYSTEM_EOL +
                "     * @return the {@link FieldDeclaration} created" + SYSTEM_EOL +
                "     ";
        Javadoc res = JavadocParser.parse(text);
        assertEquals(new Javadoc(JavadocDescription.parseText("Add a field to this and automatically add the import of the type if needed"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("typeClass", "the type of the field" + SYSTEM_EOL + "    continued in a second line"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("name", "the name of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("modifiers", "the modifiers like {@link Modifier#PUBLIC}"))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.RETURN, "the {@link FieldDeclaration} created")), res);
    }

    @Test
    void startsWithAsteriskEmpty() {
        assertEquals(-1, JavadocParser.startsWithAsterisk(""));
    }

    @Test
    void startsWithAsteriskNoAsterisk() {
        assertEquals(-1, JavadocParser.startsWithAsterisk(" ciao"));
    }

    @Test
    void startsWithAsteriskAtTheBeginning() {
        assertEquals(0, JavadocParser.startsWithAsterisk("* ciao"));
    }

    @Test
    void startsWithAsteriskAfterSpaces() {
        assertEquals(3, JavadocParser.startsWithAsterisk("   * ciao"));
    }

}
