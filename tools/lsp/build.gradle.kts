plugins {
    id("standard-kotlin")
    kotlin("plugin.serialization") version libs.versions.kotlin.get()
    id("com.gradleup.shadow") version "9.3.2"
    id("application")
}

version = "1.0-SNAPSHOT"

dependencies {
    api(project(":jmlparser-symbol-solver-core"))

    testImplementation(kotlin("test"))
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-core:1.10.0")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.10.0")
    //implementation(kotlin("serialization"))
    implementation(kotlin("serialization"))
    runtimeOnly("org.jetbrains.kotlinx:kotlinx-serialization-json:1.10.0")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.10.0")

    implementation(project(":tools:utils"))
    implementation(project(":tools:smt"))
    implementation(project(":tools:wd"))
    implementation(project(":tools:stat"))
    implementation(project(":tools:redux"))
    implementation(project(":tools:lint"))
    implementation(project(":tools:jml2java"))

    implementation("org.tinylog:tinylog-api-kotlin:2.7.0")
    implementation("org.tinylog:tinylog-api:2.8.0-M1")
    implementation("org.tinylog:tinylog-impl:2.7.0")

    implementation("org.eclipse.lsp4j:org.eclipse.lsp4j:1.0.0")

    implementation(libs.clickt)

    implementation("org.key-project:key.core:2.12.3")
    implementation("org.key-project:key.ui:2.12.3")
}

application {
    mainClass = "io.github.jmltoolkit.lsp.Main"
}