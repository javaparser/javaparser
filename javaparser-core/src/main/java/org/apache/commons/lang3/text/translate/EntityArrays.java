/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.lang3.text.translate;

/**
 * Class holding various entity data for HTML and XML - generally for use with
 * the LookupTranslator.
 * All arrays are of length [*][2].
 *
 * @since 3.0
 */
public class EntityArrays {

    /**
     * Mapping to escape the Java control characters.
     * <p>
     * Namely: {@code \b \n \t \f \r}
     *
     * @return the mapping table
     */
    public static String[][] JAVA_CTRL_CHARS_ESCAPE() {
        return JAVA_CTRL_CHARS_ESCAPE.clone();
    }

    private static final String[][] JAVA_CTRL_CHARS_ESCAPE = {
            {"\b", "\\b"},
            {"\n", "\\n"},
            {"\t", "\\t"},
            {"\f", "\\f"},
            {"\r", "\\r"}
    };

    /**
     * Reverse of {@link #JAVA_CTRL_CHARS_ESCAPE()} for unescaping purposes.
     *
     * @return the mapping table
     */
    public static String[][] JAVA_CTRL_CHARS_UNESCAPE() {
        return JAVA_CTRL_CHARS_UNESCAPE.clone();
    }

    private static final String[][] JAVA_CTRL_CHARS_UNESCAPE = invert(JAVA_CTRL_CHARS_ESCAPE);

    /**
     * Used to invert an escape array into an unescape array
     *
     * @param array String[][] to be inverted
     * @return String[][] inverted array
     */
    public static String[][] invert(final String[][] array) {
        final String[][] newarray = new String[array.length][2];
        for (int i = 0; i < array.length; i++) {
            newarray[i][0] = array[i][1];
            newarray[i][1] = array[i][0];
        }
        return newarray;
    }

}
