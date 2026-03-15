plugins {
    id("standard-kotlin")
}

dependencies {
    api(project(":jmlparser-symbol-solver-core"))
    testImplementation(libs.snakeyaml)
}
