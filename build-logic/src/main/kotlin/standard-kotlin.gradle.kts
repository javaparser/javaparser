plugins {
    kotlin("jvm")
    id("buildlogic.java-conventions")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

dependencies {}

testing {
    suites {
        val test by getting(JvmTestSuite::class) {
            useKotlinTest()
        }
    }
}


repositories {
    mavenLocal()
    mavenCentral()
    //maven(url = "https://s01.oss.sonatype.org/content/repositories/snapshots/")
}

dependencies {
    //truth = { module = "com.google.truth:truth", version = "1.10.1" }

    api(project(":jmlparser-core"))


    testImplementation(libs.findBundle("testing").get())
    testRuntimeOnly(libs.findBundle("testing-runtime").get())
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

