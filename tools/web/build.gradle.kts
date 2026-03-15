plugins {
    id("standard-kotlin")
}


dependencies {
    testImplementation("org.jetbrains.kotlin:kotlin-test")
    api(project(":jmlparser-symbol-solver-core"))

    implementation(libs.ktor.core)
    implementation(libs.ktor.html)
    implementation(libs.ktor.netty)
    implementation(libs.ktor.statuspages)
    implementation(libs.ktor.severhtml)
    implementation(libs.logback)
}
