plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-symbol-solver-core"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing.runtime)
}

description = "io.github.jmltoolkit:jmlparser-symbol-solver-testing"
