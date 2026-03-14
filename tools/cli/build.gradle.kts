plugins {
    id("standard-kotlin")
}

dependencies {
    implementation(libs.clickt)
    implementation(libs.jmlcore)
    implementation(project(":wd"))
    implementation(project(":xpath"))
    implementation(project(":prettyprinting"))
    implementation(project(":lint"))
    implementation(project(":stat"))
    implementation(project(":jml2java"))
}