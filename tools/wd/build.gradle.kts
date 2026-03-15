plugins {
    id("standard-kotlin")
}

dependencies {
    api(project(":jmlparser-symbol-solver-core"))
    api(project(":tools:smt"))
}
