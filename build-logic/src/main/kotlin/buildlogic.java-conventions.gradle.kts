@file:Suppress("UnstableApiUsage")

plugins {
    `java-library`
    id("test-report-aggregation")
    id("com.diffplug.spotless")
    checkstyle
    id("com.github.ben-manes.versions")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

group = "io.github.jmltoolkit"
version = project.properties["version"] ?: "unspecified"

repositories {
    mavenCentral()
}

dependencies {
}

// Apply a specific Java toolchain to ease working on different environments.

java {
    // Auto JDK setup
    toolchain {
        libs.findVersion("jdk").ifPresent {
            languageVersion.set(JavaLanguageVersion.of(it.toString()))
        }
    }
    //withSourcesJar()
    //withJavadocJar()
}

tasks.withType<JavaCompile> {
    options.encoding = "UTF-8"
    options.compilerArgs.add("-parameters")
}

tasks.withType<Javadoc> {
    val options = options as StandardJavadocDocletOptions
    options.encoding = "UTF-8"
    isFailOnError = false
    options.addBooleanOption("Xdoclint:none", true)
    options.addBooleanOption("html5", true)
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useJUnitJupiter()
        }
    }
}

configure<com.diffplug.gradle.spotless.SpotlessExtension> {
    java {
        targetExclude("build/generated-src/**")
        removeUnusedImports()
        palantirJavaFormat(libs.findVersion("palantirJavaFormat").get().toString()).formatJavadoc(false).style("PALANTIR")
    }
}

configure<CheckstyleExtension> {
    toolVersion = libs.findVersion("checkstyleVersion").get().toString()
    configFile = file("$rootDir/dev-files/JavaParser-CheckStyle.xml")
    isShowViolations = true
}

tasks.checkstyleMain {
    source("src/main/java")
    exclude("**/build/generated-src/**")
}