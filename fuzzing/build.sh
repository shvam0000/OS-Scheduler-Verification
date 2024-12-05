#!/bin/bash

rm -rf build
mkdir build
cmake -DFREERTOS_PORT=GCC_ARM_CM3 -B build -S .
