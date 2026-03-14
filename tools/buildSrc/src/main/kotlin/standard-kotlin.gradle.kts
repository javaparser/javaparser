plugins {
    kotlin("jvm")
    `java-library`
}

group = "io.github.jmltoolkit"


val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

dependencies {
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useKotlinTest()
        }
    }
}

// Apply a specific Java toolchain to ease working on different environments.
java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(21))
    }
}


repositories {
    mavenLocal()
    mavenCentral()
    //maven(url = "https://s01.oss.sonatype.org/content/repositories/snapshots/")
}

dependencies {
    //truth = { module = "com.google.truth:truth", version = "1.10.1" }
    testImplementation(libs.findLibrary("truth").get())
    api(libs.findLibrary("jmlcore").get()) { isChanging = true}

    testImplementation("org.junit.jupiter:junit-jupiter-engine")
    testImplementation("org.junit.jupiter:junit-jupiter-params")
}

tasks.named<Test>("test") {
    useJUnitPlatform()

    maxHeapSize = "1G"

    testLogging {
        events("passed")
    }
}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            //useKotlinTest("1.9.20")
            useJUnitJupiter()
        }
    }
}

java {
    // Auto JDK setup
    toolchain {
        languageVersion.set(JavaLanguageVersion.of("21"))
    }
    withSourcesJar()
    withJavadocJar()
}

tasks.compileJava {
    // See: https://docs.oracle.com/en/java/javase/12/tools/javac.html
    @Suppress("SpellCheckingInspection")
    options.compilerArgs.addAll(
        listOf(
            "-Xlint:all", // Enables all recommended warnings.
            "-Werror" // Terminates compilation when warnings occur.
        )
    )
    options.encoding = "UTF-8"
}

tasks.jar {
    manifest {
        attributes(
            mapOf(
                "Implementation-Title" to project.name,
                "Implementation-Version" to project.version
            )
        )
    }
}

