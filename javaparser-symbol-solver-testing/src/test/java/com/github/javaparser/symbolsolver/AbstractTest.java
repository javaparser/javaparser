/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver;

import java.io.File;

public abstract class AbstractTest {

    protected static File adaptPath(File path) {
        if (path.exists()) {
            return path;
        } else {
            File underJavaParserCore = new File("javaparser-symbol-solver-testing/" + path.getPath());
            if (underJavaParserCore.exists()) {
                return underJavaParserCore;
            } else {
                throw new IllegalArgumentException("I cannot adapt the path " + path.getAbsolutePath());
            }
        }
    }

    protected static String adaptPath(String path) {
        return adaptPath(new File(path)).getPath();
    }

    protected boolean isJava9() {
        return System.getProperty("java.version").startsWith("9.");
    }

    protected boolean isJava8() {
        return System.getProperty("java.version").startsWith("1.8.");
    }
}
