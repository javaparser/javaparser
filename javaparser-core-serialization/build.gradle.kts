plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-core"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing)

    api(libs.jakarta.json.jakarta.json.api)
    testImplementation(libs.org.eclipse.parsson.parsson)
}

description = "io.github.jmltoolkit:jmlparser-core-serialization"
