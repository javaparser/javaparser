#!/bin/sh

echo ${pwd}

docker build --tag jpbuild:1.1 --file ./dev-files/docker_trigger_release/Dockerfile . 

docker run \
    -v /home/jp-docker/.m2:/root/.m2 \
    -v /home/jp-docker/.ssh:/root/.ssh \
    jpbuild:1.1
