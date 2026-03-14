plugins {
    id("standard-kotlin")
}
dependencies {
    api(libs.jmlcore)
    implementation(project(":utils"))
    implementation("com.google.googlejavaformat:google-java-format:1.35.0")
}
