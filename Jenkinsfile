pipeline {
    agent {
        docker {
            image 'maven:latest'
        }
    }

    environment {
        MAVEN_CLI_OPTS =  "--batch-mode" // -s .m2/settings.xml
        MAVEN_OPTS =  "-Dmaven.repo.local=.m2/repository"
    }

    stages {
        stage('Clean') {
            steps {
                sh 'javac -version'
                sh 'mvn -version'
                sh 'mvn clean'
            }
        }

        stage('Compile') {
            steps { 
                sh 'mvn compile'
            }
        }

        stage('Tests: JUnit') {
            steps {
                sh 'mvn -Dmaven.test.failure.ignore=true install'
            }
            post {
                success {
                    junit '*/target/surefire-reports/**/*.xml'
                }
            }
        }
    }
}
