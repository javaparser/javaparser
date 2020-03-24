# a tiny linux distribution:
FROM alpine
# get a package list:
RUN apk update
# install the packages we need:
# (can be improved with using fixed versions?)
RUN apk add openjdk8 git maven
# copy the source code from our non-docker checkout into /javaparser:
# (maybe check out master after this?)
COPY . /javaparser
# use that as the working directory:
WORKDIR /javaparser
# start a release: (can be overridden with --run from the command line)
# (do something about the version number prompt. You will need to attach a console for that right now)
CMD mvn release:clean release:prepare release:perform  -DinteractiveMode=false 