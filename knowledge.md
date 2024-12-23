# Steps to install and work

1.  Install CBMC and FreeRTOS using `git` or `homebrew`.
2.  `scheduler_example.c` file is used to simulate FreeRTOS scheduler behaviour
3.  `FreeRTOSConfig.h` file is used to change config fo CBMC
4.  `schedule_harness.c` file is used as a CBMC test case
5.  Commands to run the CBMC example

Compilation -

```
cbmc scheduler_example.c -I/path/to/FreeRTOS-Kernel/include \
    -I/path/to/FreeRTOSConfig.h \
    -D__CPROVER__ -o scheduler
```

> add -v for verbose errors/warnings

Verification of Scheuler

```
cbmc scheduler --function CBMC_RunScheduler
```

Command which worked (this has all the configs for the FreeRTOS Config, keeping it as simple in the beginning)

Use -D to Define Missing Macros

```
cbmc scheduler_example.c \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/include" \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/portable/GCC/ARM_CM4F" \
    -DconfigUSE_IDLE_HOOK=0 \
    -DconfigUSE_TICK_HOOK=0 \
    -DconfigMAX_SYSCALL_INTERRUPT_PRIORITY=0 \
    -DconfigKERNEL_INTERRUPT_PRIORITY=0 \
    -DconfigPRIO_BITS=3 \
    --function CBMC_RunScheduler
```

6. `include` directory has all the header files
7. For Silicon based mac we use `GCC/ARM_CM4F` compiler
8. We can use `--show-symbol-tables` flag to check available functions
9. We can use `--preprocess` flag to ensure the function is included in the preprocessed output
