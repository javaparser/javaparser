plugins {
    id("standard-kotlin")
}

dependencies {
    api(libs.jmlcore)
    api(libs.jmlsymbol)
    api(project(":smt"))
}
