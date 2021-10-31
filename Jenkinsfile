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
                sh 'mvn $MAVEN_CLI_OPTS -version'
                sh 'mvn $MAVEN_CLI_OPTS dependency:go-offline'
                sh 'mvn clean'
            }
        }

        stage('Compile') {
            steps { 
                sh 'mvn $MAVEN_CLI_OPTS –o  compile'
            }
        }

        stage('Tests: JUnit') {
            steps {
                sh 'mvn $MAVEN_CLI_OPTS -o -Dmaven.test.failure.ignore=true install'
            }
            post {
                success {
                    junit '*/target/surefire-reports/**/*.xml'
                }
            }
        }
    }
}
