plugins {
    id("buildlogic.java-conventions")
    `javacc`
}

dependencies {
    api(libs.org.jspecify.jspecify)
    api(libs.net.bytebuddy.byte.buddy.agent)
}

description = "io.github.jmltoolkit:jmlparser-core"
