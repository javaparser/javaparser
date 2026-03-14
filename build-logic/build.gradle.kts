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
}
