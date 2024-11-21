// #include "FreeRTOSConfig.h"
// #include "FreeRTOS.h"
// #include "task.h"


// Created to write the test harness for the scheduler (scheduler_example.c)

#include "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "task.h"

void CBMC_RunScheduler() {
    // Initialize tasks
    xTaskCreate(task1, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
    xTaskCreate(task2, "Task2", configMINIMAL_STACK_SIZE, NULL, 2, NULL);

    // Start the scheduler
    vTaskStartScheduler();

    // Scheduler should never return
    __CPROVER_assert(0, "Scheduler returned unexpectedly!");
}