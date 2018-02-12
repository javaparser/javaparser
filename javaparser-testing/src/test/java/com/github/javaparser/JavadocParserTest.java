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

import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.JavadocBlockTag;
import com.github.javaparser.javadoc.description.JavadocDescription;
import org.junit.Assert;
import org.junit.Test;

import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.assertEquals;

public class JavadocParserTest {

    @Test
    public void parseSimplestContent() {
        Assert.assertEquals(new Javadoc(JavadocDescription.parseText("A simple line of text")),
                JavadocParser.parse("A simple line of text"));
    }

    @Test
    public void parseSingleLineWithSpacing() {
        assertEquals(new Javadoc(JavadocDescription.parseText("The line number of the first character of this Token.")),
                JavadocParser.parse(" The line number of the first character of this Token. "));
    }

    @Test
    public void parseSingleLineWithNewLines() {
        assertEquals(new Javadoc(JavadocDescription.parseText("The string image of the token.")),
                JavadocParser.parse(EOL +
                        "   * The string image of the token." + EOL +
                        "   "));
    }

    @Test
    public void parseCommentWithNewLines() {
        String text = EOL +
                "   * The version identifier for this Serializable class." + EOL +
                "   * Increment only if the <i>serialized</i> form of the" + EOL +
                "   * class changes." + EOL +
                "   ";
        assertEquals(new Javadoc(JavadocDescription.parseText("The version identifier for this Serializable class." + EOL +
                        "Increment only if the <i>serialized</i> form of the" + EOL +
                        "class changes.")),
                JavadocParser.parse(text));
    }

    @Test
    public void parseCommentWithIndentation() {
        String text = "Returns a new Token object, by default." + EOL +
                "   * However, if you want, you can create and return subclass objects based on the value of ofKind." + EOL +
                "   *" + EOL +
                "   *    case MyParserConstants.ID : return new IDToken(ofKind, image);" + EOL +
                "   *" + EOL +
                "   * to the following switch statement. Then you can cast matchedToken";
        assertEquals(new Javadoc(JavadocDescription.parseText("Returns a new Token object, by default." + EOL +
                        "However, if you want, you can create and return subclass objects based on the value of ofKind." + EOL +
                        EOL +
                        "   case MyParserConstants.ID : return new IDToken(ofKind, image);" + EOL +
                        EOL +
                        "to the following switch statement. Then you can cast matchedToken")),
                JavadocParser.parse(text));
    }

    @Test
    public void parseBlockTagsAndEmptyDescription() {
        String text = EOL +
                "   * @deprecated" + EOL +
                "   * @see #getEndColumn" + EOL +
                "   ";
        assertEquals(new Javadoc(JavadocDescription.parseText(""))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.DEPRECATED, ""))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.SEE, "#getEndColumn")), JavadocParser.parse(text));
    }

    @Test
    public void parseBlockTagsAndProvideTagName() {
        String expectedText = EOL +
                "   * @unofficial" + EOL + " " +
                "   ";

        Javadoc underTest = new Javadoc(JavadocDescription.parseText(""))
                .addBlockTag(new JavadocBlockTag("unofficial", ""));


        assertEquals(underTest, JavadocParser.parse(expectedText));
        assertEquals(1, underTest.getBlockTags().size());
        assertEquals("unofficial", underTest.getBlockTags().get(0).getTagName());
    }

    @Test
    public void parseParamBlockTags() {
        String text = EOL +
                "     * Add a field to this and automatically add the import of the type if needed" + EOL +
                "     *" + EOL +
                "     * @param typeClass the type of the field" + EOL +
                "     * @param name the name of the field" + EOL +
                "     * @param modifiers the modifiers like {@link Modifier#PUBLIC}" + EOL +
                "     * @return the {@link FieldDeclaration} created" + EOL +
                "     ";
        Javadoc res = JavadocParser.parse(text);
        assertEquals(new Javadoc(JavadocDescription.parseText("Add a field to this and automatically add the import of the type if needed"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("typeClass", "the type of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("name", "the name of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("modifiers", "the modifiers like {@link Modifier#PUBLIC}"))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.RETURN, "the {@link FieldDeclaration} created")), res);
    }

    @Test
    public void parseMultilineParamBlockTags() {
        String text = EOL +
                "     * Add a field to this and automatically add the import of the type if needed" + EOL +
                "     *" + EOL +
                "     * @param typeClass the type of the field" + EOL +
                "     *     continued in a second line" + EOL +
                "     * @param name the name of the field" + EOL +
                "     * @param modifiers the modifiers like {@link Modifier#PUBLIC}" + EOL +
                "     * @return the {@link FieldDeclaration} created" + EOL +
                "     ";
        Javadoc res = JavadocParser.parse(text);
        assertEquals(new Javadoc(JavadocDescription.parseText("Add a field to this and automatically add the import of the type if needed"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("typeClass", "the type of the field" + EOL + "    continued in a second line"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("name", "the name of the field"))
                .addBlockTag(JavadocBlockTag.createParamBlockTag("modifiers", "the modifiers like {@link Modifier#PUBLIC}"))
                .addBlockTag(new JavadocBlockTag(JavadocBlockTag.Type.RETURN, "the {@link FieldDeclaration} created")), res);
    }

    @Test
    public void startsWithAsteriskEmpty() {
        assertEquals(-1, JavadocParser.startsWithAsterisk(""));
    }

    @Test
    public void startsWithAsteriskNoAsterisk() {
        assertEquals(-1, JavadocParser.startsWithAsterisk(" ciao"));
    }

    @Test
    public void startsWithAsteriskAtTheBeginning() {
        assertEquals(0, JavadocParser.startsWithAsterisk("* ciao"));
    }

    @Test
    public void startsWithAsteriskAfterSpaces() {
        assertEquals(3, JavadocParser.startsWithAsterisk("   * ciao"));
    }

}
