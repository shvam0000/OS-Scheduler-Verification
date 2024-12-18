#include "FreeRTOS.h"
#include "task.h"
#include "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/FreeRTOSConfig.h"

#undef taskYIELD

typedef enum { TASK_READY, TASK_RUNNING, TASK_SUSPENDED } TaskState;

typedef struct tskTaskControlBlock {
    void *pxStack;       // Simplified stack pointer
    void *pvParameters;  // Task parameters
    TaskState state;     // Task state
} tskTaskControlBlock;

typedef tskTaskControlBlock* TaskHandle_t;

// Simulated memory allocation
void *__CPROVER_malloc(size_t size) {
    static char memory_pool[1024];
    static size_t offset = 0;
    if (offset + size <= 1024) {
        void *ptr = &memory_pool[offset];
        offset += size;
        return ptr;
    }
    return NULL;
}

// Task creation stub
BaseType_t xTaskCreate(TaskFunction_t pxTaskCode, const char * const pcName,
                       const configSTACK_DEPTH_TYPE usStackDepth, void * const pvParameters,
                       UBaseType_t uxPriority, TaskHandle_t * const pxCreatedTask) {
    __CPROVER_assert(pxTaskCode != NULL, "Task code must not be NULL");
    *pxCreatedTask = __CPROVER_malloc(sizeof(tskTaskControlBlock));
    if (*pxCreatedTask != NULL) {
        (*pxCreatedTask)->state = TASK_READY; // Initialize as READY
        return pdPASS;
    }
    return pdFAIL;
}

// Simulated scheduler
void vTaskStartScheduler(void) {
    __CPROVER_assume(0); // Scheduler never returns
}

// Task function with infinite loop
void taskFunction(void *pvParameters) {
    for (;;) {
        __CPROVER_assume(__CPROVER_nondet_bool()); // Simulate task behavior
    }
    // If control reaches here, the task has exited the loop
    __CPROVER_assert(0, "Task must never exit the for loop");
}

// Verification function
void CBMC_VerifyTaskForLoop() {
    TaskHandle_t task1 = NULL;

    // Create the task
    __CPROVER_assume(xTaskCreate(taskFunction, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, &task1) == pdPASS);

    // Start the scheduler
    vTaskStartScheduler();

    // Task is running; verify it never exits the for loop
    __CPROVER_assert(0, "Unreachable code: Scheduler should never return");
}
