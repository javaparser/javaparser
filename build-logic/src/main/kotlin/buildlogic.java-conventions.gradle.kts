plugins {
    `java-library`
    `maven-publish`
    id("test-report-aggregation")
    id("com.diffplug.spotless")
    checkstyle
}

group = "io.github.jmltoolkit"
version = "3.28.0-J8.0-K13.5"

repositories {
    maven {
        url = uri("https://repo.maven.apache.org/maven2/")
    }
}

dependencies {
}

java.sourceCompatibility = JavaVersion.VERSION_21

publishing {
    publications.create<MavenPublication>("maven") {
        from(components["java"])
    }
}

tasks.withType<JavaCompile> {
    options.encoding = "UTF-8"
}

tasks.withType<Javadoc> {
    options.encoding = "UTF-8"
}

tasks.withType<Test> {
    workingDir = projectDir
    useJUnitPlatform()
}

configure<com.diffplug.gradle.spotless.SpotlessExtension> {
    java {
        removeUnusedImports()
        palantirJavaFormat("2.86.0").formatJavadoc(false).style("PALANTIR")
    }
}

configure<CheckstyleExtension> {
    toolVersion = "13.1.0"
    configFile = file("$rootDir/dev-files/JavaParser-CheckStyle.xml")
    isShowViolations = true
}


tasks.checkstyleMain {
    source("src/main/java")
}

