pipeline {
    agent {
        docker {
            image 'maven:latest'
        }
    }

    environment {
      // This will suppress any download for dependencies and plugins or upload messages which would clutter the console log.
      //`showDateTime` will show the passed time in milliseconds. You need to specify `--batch-mode` to make this work.
      MAVEN_OPTS: "-Dmaven.repo.local=.m2/repository -Dorg.slf4j.simpleLogger.log.org.apache.maven.cli.transfer.Slf4jMavenTransferListener=WARN -Dorg.slf4j.simpleLogger.showDateTime=true -Djava.awt.headless=true"
      // As of Maven 3.3.0 instead of this you may define these options in `.mvn/maven.config` so the same config is used
      // when running from the command line.
      // `installAtEnd` and `deployAtEnd` are only effective with recent version of the corresponding plugins.
      MAVEN_CLI_OPTS: "--batch-mode --errors --fail-at-end --show-version -DinstallAtEnd=true -DdeployAtEnd=true"
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
                sh 'mvn --offline $MAVEN_CLI_OPTS compile'
            }
        }

        stage('Tests: JUnit') {
            steps {
                sh 'mvn --offline $MAVEN_CLI_OPTS -Dmaven.test.failure.ignore=true install'
            }
            post {
                success {
                    junit '*/target/surefire-reports/**/*.xml'
                }
            }
        }
    }
}
