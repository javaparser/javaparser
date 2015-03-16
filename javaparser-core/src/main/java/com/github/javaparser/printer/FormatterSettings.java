/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.printer;

/**
 * @author Didier Villevalois
 */
public class FormatterSettings {

    public static FormatterSettings DEFAULT = new FormatterSettings();

    public enum IndentationContext {
        TYPE_BODY,
        BLOCK,
        PARAMETERS,
        STATEMENT,
        SWITCH,
        SWITCH_CASE,
        IF_ELSE,
        TRY_RESOURCES,
        // Keep the last comma
        ;
    }

    public enum EmptyLineLocation {
        AFTER_PACKAGE_DECLARATION,
        AFTER_IMPORT_DECLARATIONS,
        BETWEEN_TOP_LEVEL_DECLARATIONS,
        BEFORE_MEMBERS,
        BETWEEN_MEMBERS,
        AFTER_MEMBERS,
        // Keep the last comma
        ;
    }

    public int indentation(IndentationContext context) {
        switch (context) {
            case TYPE_BODY:
                return 1;
            case BLOCK:
                return 1;
            case PARAMETERS:
                return 2;
            case STATEMENT:
                return 2;
            case SWITCH:
                return 1;
            case SWITCH_CASE:
                return 1;
            case IF_ELSE:
                return 1;
            case TRY_RESOURCES:
                return 2;
            default:
                return 1;
        }
    }

    public int emptyLineCount(EmptyLineLocation location) {
        switch (location) {
            case AFTER_PACKAGE_DECLARATION:
                return 1;
            case AFTER_IMPORT_DECLARATIONS:
                return 1;
            case BETWEEN_TOP_LEVEL_DECLARATIONS:
                return 1;
            case BEFORE_MEMBERS:
                return 1;
            case BETWEEN_MEMBERS:
                return 1;
            case AFTER_MEMBERS:
                return 1;
            default:
                return 1;
        }
    }
}
