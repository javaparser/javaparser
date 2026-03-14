plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-core"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing.runtime)
}

description = "io.github.jmltoolkit:jmlparser-core-testing-bdd"
