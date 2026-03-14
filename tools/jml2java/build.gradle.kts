plugins {
    id("standard-kotlin")
}

dependencies {
    api(project(":utils"))
    testImplementation(kotlin("serialization"))
    testImplementation(libs.snakeyaml)
}
