#!/bin/sh

docker build --tag jpbuild:1.1 --file ./dev-files/docker_trigger_release/Dockerfile . 

docker run jpbuild:1.1
