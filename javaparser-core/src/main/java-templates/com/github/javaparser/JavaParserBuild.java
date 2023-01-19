/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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

/**
 * Some information that was available when this library was built by Maven.
 */
public class JavaParserBuild {
    public static final String PROJECT_VERSION = "${project.version}";
    public static final String PROJECT_NAME = "${project.name}";
    public static final String PROJECT_BUILD_FINAL_NAME = "${project.build.finalName}";
    public static final String MAVEN_VERSION = "${maven.version}";
    public static final String MAVEN_BUILD_VERSION = "${maven.build.version}";
    public static final String MAVEN_BUILD_TIMESTAMP = "${build.timestamp}";
    public static final String JAVA_VENDOR ="${java.vendor}";
    public static final String JAVA_VENDOR_URL ="${java.vendor.url}";
    public static final String JAVA_VERSION ="${java.version}";
    public static final String OS_ARCH ="${os.arch}";
    public static final String OS_NAME ="${os.name}";
    public static final String OS_VERSION ="${os.version}";
}