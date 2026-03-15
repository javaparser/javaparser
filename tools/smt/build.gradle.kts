plugins {
    id("standard-kotlin")
}

dependencies {
    //implementation(libs)
    implementation(project(":tools:utils"))


    testImplementation(libs.snakeyaml)
}
