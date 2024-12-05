[![CMock Unit Tests](https://github.com/FreeRTOS/FreeRTOS-Kernel/actions/workflows/unit-tests.yml/badge.svg?branch=main&event=push)](https://github.com/FreeRTOS/FreeRTOS-Kernel/actions/workflows/unit-tests.yml?query=branch%3Amain+event%3Apush+workflow%3A%22CMock+Unit+Tests%22++)
[![codecov](https://codecov.io/gh/FreeRTOS/FreeRTOS-Kernel/badge.svg?branch=main)](https://codecov.io/gh/FreeRTOS/FreeRTOS-Kernel)

## Getting started

This repository contains FreeRTOS kernel source/header files and kernel
ports only. This repository is referenced as a submodule in
[FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS)
repository, which contains pre-configured demo application projects under
`FreeRTOS/Demo` directory.

The easiest way to use FreeRTOS is to start with one of the pre-configured demo
application projects. That way you will have the correct FreeRTOS source files
included, and the correct include paths configured. Once a demo application is
building and executing you can remove the demo application files, and start to
add in your own application source files. See the
[FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/Documentation/01-FreeRTOS-quick-start/01-Beginners-guide/02-Quick-start-guide)
for detailed instructions and other useful links.

Additionally, for FreeRTOS kernel feature information refer to the
[Developer Documentation](https://www.freertos.org/Documentation/02-Kernel/02-Kernel-features/00-Developer-docs),
and [API Reference](https://www.freertos.org/Documentation/02-Kernel/04-API-references/01-Task-creation/00-TaskHandle).

Also for contributing and creating a Pull Request please refer to
[the instructions here](.github/CONTRIBUTING.md#contributing-via-pull-request).

**FreeRTOS-Kernel V11.1.0
[source code](https://github.com/FreeRTOS/FreeRTOS-Kernel/tree/V11.1.0) is part
of the
[FreeRTOS 202406.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202406-LTS)
release.**

### Getting help

If you have any questions or need assistance troubleshooting your FreeRTOS project,
we have an active community that can help on the
[FreeRTOS Community Support Forum](https://forums.freertos.org).

## To consume FreeRTOS-Kernel

### Consume with CMake

If using CMake, it is recommended to use this repository using FetchContent.
Add the following into your project's main or a subdirectory's `CMakeLists.txt`:

- Define the source and version/tag you want to use:

```cmake
FetchContent_Declare( freertos_kernel
  GIT_REPOSITORY https://github.com/FreeRTOS/FreeRTOS-Kernel.git
  GIT_TAG        main #Note: Best practice to use specific git-hash or tagged version
)
```

In case you prefer to add it as a git submodule, do:

```bash
git submodule add https://github.com/FreeRTOS/FreeRTOS-Kernel.git <path of the submodule>
git submodule update --init
```

- Add a freertos_config library (typically an INTERFACE library) The following assumes the directory structure:
  - `include/FreeRTOSConfig.h`

```cmake
add_library(freertos_config INTERFACE)

target_include_directories(freertos_config SYSTEM
INTERFACE
    include
)

target_compile_definitions(freertos_config
  INTERFACE
    projCOVERAGE_TEST=0
)
```

In case you installed FreeRTOS-Kernel as a submodule, you will have to add it as a subdirectory:

```cmake
add_subdirectory(${FREERTOS_PATH})
```

- Configure the FreeRTOS-Kernel and make it available
  - this particular example supports a native and cross-compiled build option.

```cmake
set( FREERTOS_HEAP "4" CACHE STRING "" FORCE)
# Select the native compile PORT
set( FREERTOS_PORT "GCC_POSIX" CACHE STRING "" FORCE)
# Select the cross-compile PORT
if (CMAKE_CROSSCOMPILING)
  set(FREERTOS_PORT "GCC_ARM_CA9" CACHE STRING "" FORCE)
endif()

FetchContent_MakeAvailable(freertos_kernel)
```

- In case of cross compilation, you should also add the following to `freertos_config`:

```cmake
target_compile_definitions(freertos_config INTERFACE ${definitions})
target_compile_options(freertos_config INTERFACE ${options})
```

### Consuming stand-alone - Cloning this repository

To clone using HTTPS:

```
git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git
```

Using SSH:

```
git clone git@github.com:FreeRTOS/FreeRTOS-Kernel.git
```

## Repository structure

- The root of this repository contains the three files that are common to
  every port - list.c, queue.c and tasks.c. The kernel is contained within these
  three files. croutine.c implements the optional co-routine functionality - which
  is normally only used on very memory limited systems.

- The `./portable` directory contains the files that are specific to a particular microcontroller and/or compiler.
  See the readme file in the `./portable` directory for more information.

- The `./include` directory contains the real time kernel header files.

- The `./template_configuration` directory contains a sample `FreeRTOSConfig.h` to help jumpstart a new project.
  See the [FreeRTOSConfig.h](examples/template_configuration/FreeRTOSConfig.h) file for instructions.

### Code Formatting

FreeRTOS files are formatted using the
"[uncrustify](https://github.com/uncrustify/uncrustify)" tool.
The configuration file used by uncrustify can be found in the
[FreeRTOS/CI-CD-GitHub-Actions's](https://github.com/FreeRTOS/CI-CD-Github-Actions)
[uncrustify.cfg](https://github.com/FreeRTOS/CI-CD-Github-Actions/tree/main/formatting)
file.

### Line Endings

File checked into the FreeRTOS-Kernel repository use unix-style LF line endings
for the best compatibility with git.

For optimal compatibility with Microsoft Windows tools, it is best to enable
the git autocrlf feature. You can enable this setting for the current
repository using the following command:

```
git config core.autocrlf true
```

### Git History Optimizations

Some commits in this repository perform large refactors which touch many lines
and lead to unwanted behavior when using the `git blame` command. You can
configure git to ignore the list of large refactor commits in this repository
with the following command:

```
git config blame.ignoreRevsFile .git-blame-ignore-revs
```

### Spelling and Formatting

We recommend using [Visual Studio Code](https://code.visualstudio.com),
commonly referred to as VSCode, when working on the FreeRTOS-Kernel.
The FreeRTOS-Kernel also uses [cSpell](https://cspell.org/) as part of its
spelling check. The config file for which can be found at [cspell.config.yaml](cspell.config.yaml)
There is additionally a
[cSpell plugin for VSCode](https://marketplace.visualstudio.com/items?itemName=streetsidesoftware.code-spell-checker)
that can be used as well.
_[.cSpellWords.txt](.github/.cSpellWords.txt)_ contains words that are not
traditionally found in an English dictionary. It is used by the spellchecker
to verify the various jargon, variable names, and other odd words used in the
FreeRTOS code base are correct. If your pull request fails to pass the spelling
and you believe this is a mistake, then add the word to
_[.cSpellWords.txt](.github/.cSpellWords.txt)_. When adding a word please
then sort the list, which can be done by running the bash command:
`sort -u .cSpellWords.txt -o .cSpellWords.txt`
Note that only the FreeRTOS-Kernel Source Files, [include](include),
[portable/MemMang](portable/MemMang), and [portable/Common](portable/Common)
files are checked for proper spelling, and formatting at this time.

## Third Party Tools

Visit [this link](.github/third_party_tools.md) for detailed information about
third-party tools with FreeRTOS support.

# Fuzzing Steps

## Stuck

```
mkdir build
cd build
cmake -DFREERTOS_PORT=GCC_ARM_CM4F ..
make
```
This is not able to build the kernel, getting the following error message on my machine

```
/tmp/ccM46PL2.s: Assembler messages:
/tmp/ccM46PL2.s:77: Error: unknown or missing system register name at operand 1 -- `msr basepri,x0'
/tmp/ccM46PL2.s:79: Error: missing immediate expression at operand 1 -- `dsb '
/tmp/ccM46PL2.s:106: Error: expected a register at operand 1 -- `ldr r3,=pxCurrentTCB'
/tmp/ccM46PL2.s:107: Error: expected a register at operand 1 -- `ldr r1,[r3]'
/tmp/ccM46PL2.s:108: Error: expected a register at operand 1 -- `ldr r0,[r1]'
/tmp/ccM46PL2.s:109: Error: unknown mnemonic `ldmia' -- `ldmia r0!,{r4-r11,r14}'
/tmp/ccM46PL2.s:110: Error: unknown or missing system register name at operand 1 -- `msr psp,r0'
/tmp/ccM46PL2.s:112: Error: expected a register or register list at operand 1 -- `mov r0,#0'
/tmp/ccM46PL2.s:113: Error: unknown or missing system register name at operand 1 -- `msr basepri,r0'
/tmp/ccM46PL2.s:114: Error: unknown mnemonic `bx' -- `bx r14'
/tmp/ccM46PL2.s:132: Error: expected a register at operand 1 -- `ldr r0,=0xE000ED08'
/tmp/ccM46PL2.s:133: Error: expected a register at operand 1 -- `ldr r0,[r0]'
/tmp/ccM46PL2.s:134: Error: expected a register at operand 1 -- `ldr r0,[r0]'
/tmp/ccM46PL2.s:135: Error: unknown or missing system register name at operand 1 -- `msr msp,r0'
/tmp/ccM46PL2.s:136: Error: expected a register or register list at operand 1 -- `mov r0,#0'
/tmp/ccM46PL2.s:137: Error: unknown or missing system register name at operand 1 -- `msr control,r0'
/tmp/ccM46PL2.s:138: Error: unknown mnemonic `cpsie' -- `cpsie i'
/tmp/ccM46PL2.s:139: Error: unknown mnemonic `cpsie' -- `cpsie f'
/tmp/ccM46PL2.s:140: Error: missing immediate expression at operand 1 -- `dsb '
/tmp/ccM46PL2.s:231: Error: unknown or missing system register name at operand 1 -- `msr basepri,x0'
/tmp/ccM46PL2.s:233: Error: missing immediate expression at operand 1 -- `dsb '
/tmp/ccM46PL2.s:277: Error: unknown or missing system register name at operand 1 -- `msr basepri,x0'
/tmp/ccM46PL2.s:297: Error: expected an integer or zero register at operand 1 -- `mrs r0,psp'
/tmp/ccM46PL2.s:300: Error: expected a register at operand 1 -- `ldr r3,=pxCurrentTCB'
/tmp/ccM46PL2.s:301: Error: expected a register at operand 1 -- `ldr r2,[r3]'
/tmp/ccM46PL2.s:303: Error: expected an integer or zero register at operand 1 -- `tst r14,#0x10'
/tmp/ccM46PL2.s:304: Error: unknown mnemonic `it' -- `it eq'
/tmp/ccM46PL2.s:305: Error: unknown mnemonic `vstmdbeq' -- `vstmdbeq r0!,{s16-s31}'
/tmp/ccM46PL2.s:307: Error: unknown mnemonic `stmdb' -- `stmdb r0!,{r4-r11,r14}'
/tmp/ccM46PL2.s:308: Error: expected a register at operand 1 -- `str r0,[r2]'
/tmp/ccM46PL2.s:310: Error: unknown mnemonic `stmdb' -- `stmdb sp!,{r0,r3}'
/tmp/ccM46PL2.s:311: Error: expected a register or register list at operand 1 -- `mov r0,0'
/tmp/ccM46PL2.s:312: Error: unknown or missing system register name at operand 1 -- `msr basepri,r0'
/tmp/ccM46PL2.s:313: Error: missing immediate expression at operand 1 -- `dsb '
/tmp/ccM46PL2.s:316: Error: expected a register or register list at operand 1 -- `mov r0,#0'
/tmp/ccM46PL2.s:317: Error: unknown or missing system register name at operand 1 -- `msr basepri,r0'
/tmp/ccM46PL2.s:318: Error: unknown mnemonic `ldmia' -- `ldmia sp!,{r0,r3}'
/tmp/ccM46PL2.s:320: Error: expected a register at operand 1 -- `ldr r1,[r3]'
/tmp/ccM46PL2.s:321: Error: expected a register at operand 1 -- `ldr r0,[r1]'
/tmp/ccM46PL2.s:323: Error: unknown mnemonic `ldmia' -- `ldmia r0!,{r4-r11,r14}'
/tmp/ccM46PL2.s:325: Error: expected an integer or zero register at operand 1 -- `tst r14,#0x10'
/tmp/ccM46PL2.s:326: Error: unknown mnemonic `it' -- `it eq'
/tmp/ccM46PL2.s:327: Error: unknown mnemonic `vldmiaeq' -- `vldmiaeq r0!,{s16-s31}'
/tmp/ccM46PL2.s:329: Error: unknown or missing system register name at operand 1 -- `msr psp,r0'
/tmp/ccM46PL2.s:333: Error: unknown mnemonic `bx' -- `bx r14'
/tmp/ccM46PL2.s:358: Error: unknown or missing system register name at operand 1 -- `msr basepri,x0'
/tmp/ccM46PL2.s:360: Error: missing immediate expression at operand 1 -- `dsb '
/tmp/ccM46PL2.s:378: Error: unknown or missing system register name at operand 1 -- `msr basepri,x0'
/tmp/ccM46PL2.s:423: Error: unknown mnemonic `ldr.w' -- `ldr.w r0,=0xE000ED88'
/tmp/ccM46PL2.s:424: Error: expected a register at operand 1 -- `ldr r1,[r0]'
/tmp/ccM46PL2.s:426: Error: expected a register at operand 1 -- `orr r1,r1,#(0xf<<20)'
/tmp/ccM46PL2.s:427: Error: expected a register at operand 1 -- `str r1,[r0]'
/tmp/ccM46PL2.s:428: Error: unknown mnemonic `bx' -- `bx r14'
make[2]: *** [portable/CMakeFiles/freertos_kernel_port.dir/build.make:76: portable/CMakeFiles/freertos_kernel_port.dir/GCC/ARM_CM4F/port.c.o] Error 1
make[1]: *** [CMakeFiles/Makefile2:144: portable/CMakeFiles/freertos_kernel_port.dir/all] Error 2
make: *** [Makefile:91: all] Error 2
```
It seems like its a build target issue? but I am not entirely sure..
