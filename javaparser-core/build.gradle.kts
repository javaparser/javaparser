plugins {
    id("buildlogic.java-conventions")
    //id("org.javacc.javacc") version "4.0.3"
}

description = "io.github.jmltoolkit:jmlparser-core"

val javacc by configurations.creating

dependencies {
    api(libs.org.jspecify.jspecify)
    api(libs.net.bytebuddy.byte.buddy.agent)
    javacc("com.helger:parser-generator-cc:2.0.1")
}

val javaccOutput = layout.buildDirectory.dir("generated-src/main/javacc").get().asFile.absolutePath
val javaccInput = "src/main/javacc/java.jj"


val compileJavacc by tasks.registering(JavaExec::class) {
    inputs.file(javaccInput).withPathSensitivity(PathSensitivity.RELATIVE)
    outputs.dir(javaccOutput)
    mainClass.set("com.helger.pgcc.parser.Main")
    classpath(javacc)
    args = listOf(
        "-OUTPUT_DIRECTORY=$javaccOutput/com/github/javaparser",
        "src/main/javacc/java.jj"
    )
}
tasks.compileJava { dependsOn(compileJavacc) }
sourceSets.main {
    java {
        srcDirs(javaccOutput, "src/main/javacc-support")
    }
}