plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-core"))
    api(libs.org.javassist.javassist)
    api(libs.com.google.guava.guava)
    api(libs.org.checkerframework.checker.qual)
}

description = "io.github.jmltoolkit:jmlparser-symbol-solver-core"
