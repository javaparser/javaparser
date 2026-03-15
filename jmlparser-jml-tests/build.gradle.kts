plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    testImplementation(project(":jmlparser-core"))
    testImplementation(project(":jmlparser-symbol-solver-core"))
    testImplementation(project(":jmlparser-core-testing"))
    testImplementation(project(":jmlparser-core-testing-bdd"))
    testImplementation(project(":jmlparser-symbol-solver-testing"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing.runtime)
}

description = "io.github.jmltoolkit:jmlparser-jml-tests"
