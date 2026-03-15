import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinVersion

val libs: VersionCatalog = extensions.getByType<VersionCatalogsExtension>().named("libs")

plugins {
    `kotlin-dsl`
    `kotlin-dsl-precompiled-script-plugins`
}

repositories {
    gradlePluginPortal()
    mavenCentral()
}

dependencies {
    implementation("com.diffplug.gradle.spotless:com.diffplug.gradle.spotless.gradle.plugin:8.3.0")

    add("implementation", libs.findLibrary("kotlin-gradle").get())

    // https://github.com/Kotlin/dokka
    // Dokka is a documentation engine for Kotlin like JavaDoc for Java
    //add("implementation", libs.findLibrary("dokka-gradle").get())

    // https://detekt.dev/docs/gettingstarted/gradle/
    // A static code analyzer for Kotlin
    //add("implementation", libs.findLibrary("detekt-gradle").get())
}