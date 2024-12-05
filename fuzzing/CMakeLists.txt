cmake_minimum_required(VERSION 3.16)
project(FuzzingTarget)

# Set the C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED YES)

# Enable address sanitizer and fuzzing
set(SANITIZER_FLAGS "-fsanitize=address,fuzzer")

# Add debugging symbols
set(CMAKE_CXX_FLAGS_DEBUG "-g")

set(FREERTOS_PORT GCC_ARM_CM3 CACHE STRING "")

# Include directories
include_directories(
    ${CMAKE_SOURCE_DIR}/../include
    ${CMAKE_SOURCE_DIR}/../portable/GCC/ARM_CM4F
    ${CMAKE_SOURCE_DIR}/../config
)

# Make freertos_kernel
add_subdirectory(.. kernel)

# Add the executable
add_executable(fuzzing_target target.cc)

# Link freertos_kernel library

target_link_libraries(fuzzing_target PRIVATE freertos_kernel)

# Apply sanitization and debugging flags
target_compile_options(fuzzing_target PRIVATE ${SANITIZER_FLAGS})
target_link_options(fuzzing_target PRIVATE ${SANITIZER_FLAGS})
