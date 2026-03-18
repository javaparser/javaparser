plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-core"))
    testImplementation(libs.bundles.testing)
    testRuntimeOnly(libs.bundles.testing.runtime)
}

description = "io.github.jmltoolkit:jmlparser-core-generators"

val run by tasks.registering(JavaExec::class) {
    classpath = sourceSets.main.get().runtimeClasspath
    mainClass = "com.github.javaparser.generator.core.CoreGenerator"
    args = listOf("$projectDir")
}
