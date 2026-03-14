plugins {
    id("standard-kotlin")
}

dependencies {
    api(libs.jmlcore)
    implementation(libs.guava)
    implementation(project(":utils"))


    testImplementation(libs.snakeyaml)
}
