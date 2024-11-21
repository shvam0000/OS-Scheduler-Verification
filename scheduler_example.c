// Created to write algorithms for the FreeRTOS scheduler which we want to test on

#include "FreeRTOS.h"
#include "task.h"

void task1(void *pvParameters) {
    for (;;) {
        // Task 1 body
    }
}

void task2(void *pvParameters) {
    for (;;) {
        // Task 2 body
    }
}

void CBMC_RunScheduler() {
    xTaskCreate(task1, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
    xTaskCreate(task2, "Task2", configMINIMAL_STACK_SIZE, NULL, 2, NULL);
    vTaskStartScheduler();

    // Scheduler should never return
    __CPROVER_assert(0, "Scheduler returned unexpectedly!");
}

// Stub for xTaskCreate
BaseType_t xTaskCreate(TaskFunction_t pxTaskCode, const char * const pcName,
                       const configSTACK_DEPTH_TYPE usStackDepth, void * const pvParameters,
                       UBaseType_t uxPriority, TaskHandle_t * const pxCreatedTask) {
    __CPROVER_assert(pxTaskCode != NULL, "Task code must not be NULL");
    return 1; // Assume success
}

// Stub for vTaskStartScheduler
void vTaskStartScheduler(void) {
    while (1) {
        // Infinite loop simulating a running scheduler
    }
}

int main() {
    xTaskCreate(task1, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
    xTaskCreate(task2, "Task2", configMINIMAL_STACK_SIZE, NULL, 2, NULL);
    vTaskStartScheduler(); // Start the scheduler
    return 0;
}

// #include "FreeRTOS.h"
// #include "task.h"

// void task1(void *pvParameters) {
//     for (;;) {}
// }

// void task2(void *pvParameters) {
//     for (;;) {}
// }

// void CBMC_RunScheduler() {
//     xTaskCreate(task1, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
//     xTaskCreate(task2, "Task2", configMINIMAL_STACK_SIZE, NULL, 2, NULL);
//     vTaskStartScheduler();

//     __CPROVER_assert(0, "Scheduler returned unexpectedly!");
// }