#!/bin/bash
BASE=`dirname $0`
java -cp $BASE/classes/:$BASE/lib/antlr.jar Retreet $@
