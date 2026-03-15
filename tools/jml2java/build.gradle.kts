plugins {
    id("standard-kotlin")
}

dependencies {
    api(project(":tools:utils"))
    testImplementation(kotlin("serialization"))
    testImplementation(libs.snakeyaml)
}
