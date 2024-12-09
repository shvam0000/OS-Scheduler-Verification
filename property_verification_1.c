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

BaseType_t xTaskCreate(TaskFunction_t pxTaskCode, const char * const pcName,
                       const configSTACK_DEPTH_TYPE usStackDepth, void * const pvParameters,
                       UBaseType_t uxPriority, TaskHandle_t * const pxCreatedTask) {
    __CPROVER_assert(pxTaskCode != NULL, "Task code must not be NULL");
    *pxCreatedTask = __CPROVER_malloc(sizeof(tskTaskControlBlock));
    if (*pxCreatedTask != NULL) {
        (*pxCreatedTask)->state = TASK_READY; // Initialize as ready
        return pdPASS;  // Simulate successful task creation
    }
    return pdFAIL;
}

void vTaskSuspend(TaskHandle_t xTaskToSuspend) {
    __CPROVER_assert(xTaskToSuspend != NULL, "Task to suspend must not be NULL");
    xTaskToSuspend->state = TASK_SUSPENDED; // Change state to suspended
}

void vTaskResume(TaskHandle_t xTaskToResume) {
    __CPROVER_assert(xTaskToResume != NULL, "Task to resume must not be NULL");
    __CPROVER_assert(xTaskToResume->state == TASK_SUSPENDED, "Only a suspended task can be resumed");
    xTaskToResume->state = TASK_READY; // Change state back to ready
}

void vTaskStartScheduler(void) {
    // Simulate scheduler behavior
    __CPROVER_assume(0); // Scheduler should never return
}

void *__CPROVER_malloc(size_t size) {
    static char memory_pool[1024]; // Define a static memory pool
    static size_t offset = 0;      // Track the current offset
    if (offset + size <= 1024) {
        void *ptr = &memory_pool[offset];
        offset += size;
        return ptr;                // Return allocated memory
    }
    return NULL;                   // Return NULL if out of memory
}

void nondet_task_function(void *pvParameters) {
    for (;;) {
        if (__CPROVER_nondet_bool()) {
            // Simulate nondeterministic behavior
        } else {
            // Stay idle
        }
    }
}

void CBMC_VerifySuspension() {
    TaskHandle_t task1 = NULL;

    // Create task
    __CPROVER_assume(xTaskCreate(nondet_task_function, "Task1", configMINIMAL_STACK_SIZE, NULL, 1, &task1) == pdPASS);

    // Suspend task
    vTaskSuspend(task1);

    // Assert task remains suspended until resumed
    __CPROVER_assert(task1->state == TASK_SUSPENDED, "Task must remain suspended");

    // Verify task does not transition to ready without explicit API call
    __CPROVER_assert(task1->state != TASK_READY, "Task cannot be resumed without API call");
}
