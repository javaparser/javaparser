plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    testImplementation(project(":jmlparser-core"))
    testImplementation(project(":jmlparser-symbol-solver-core"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing.runtime)
}

description = "io.github.jmltoolkit:javaparser-key-testing"
