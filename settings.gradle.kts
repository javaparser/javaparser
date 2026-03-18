pluginManagement {
    // Include 'plugins build' to define convention plugins.
    includeBuild("build-logic")
    repositories {
        gradlePluginPortal()
        mavenCentral()
    }
}

rootProject.name = "jmlparser-parent"
include(":jmlparser-jml-tests")
include(":javaparser-key-testing")
include(":jmlparser-core-serialization")
include(":jmlparser-core-testing")
include(":jmlparser-core-testing-bdd")
include(":jmlparser-core-metamodel-generator")
include(":jmlparser-core-generators")
include(":jmlparser-core")
include(":jmlparser-symbol-solver-core")
include(":jmlparser-symbol-solver-testing")

project(":jmlparser-core-serialization").projectDir = file("javaparser-core-serialization")
project(":jmlparser-core-testing").projectDir = file("javaparser-core-testing")
project(":jmlparser-core-testing-bdd").projectDir = file("javaparser-core-testing-bdd")
project(":jmlparser-core-metamodel-generator").projectDir = file("javaparser-core-metamodel-generator")
project(":jmlparser-core-generators").projectDir = file("javaparser-core-generators")
project(":jmlparser-core").projectDir = file("javaparser-core")
project(":jmlparser-symbol-solver-core").projectDir = file("javaparser-symbol-solver-core")
project(":jmlparser-symbol-solver-testing").projectDir = file("javaparser-symbol-solver-testing")


include(":tools:stat")
include(":tools:lint")
include(":tools:smt")
include(":tools:prettyprinting")
include(":tools:utils")
include(":tools:wd")
include(":tools:redux")
include(":tools:xpath")
include(":tools:cli")
include(":tools:lsp")
include(":tools:web")
include(":tools:jml2java")
