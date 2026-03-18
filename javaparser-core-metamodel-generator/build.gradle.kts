plugins {
    id("buildlogic.java-conventions")
}

dependencies {
    api(project(":jmlparser-core"))
}

description = "io.github.jmltoolkit:jmlparser-core-metamodel-generator"

val run by tasks.registering(JavaExec::class) {
    classpath = sourceSets.main.get().runtimeClasspath
    mainClass = "com.github.javaparser.generator.metamodel.MetaModelGenerator"
    args = listOf("$projectDir")
}
