#include "FreeRTOS.h"
#include "task.h"
#include "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/FreeRTOSConfig.h"

#undef taskYIELD

typedef enum { TASK_READY, TASK_RUNNING, TASK_SUSPENDED } TaskState;

typedef struct tskTaskControlBlock {
    void *pxStack;       // Simplified stack pointer
    void *pvParameters;  // Task parameters
    TaskState state;     // Task state
    UBaseType_t priority; // Task priority
} tskTaskControlBlock;

typedef tskTaskControlBlock* TaskHandle_t;
typedef tskTaskControlBlock* TCB_t;

// CBMC-specific definitions
#ifdef __CPROVER
void __CPROVER_assert(_Bool condition, const char *description);
void __CPROVER_assume(_Bool condition);
_Bool __CPROVER_nondet_bool(void);
#endif

// Simulate __CPROVER_malloc for CBMC
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

// Simplified xTaskCreate
BaseType_t xTaskCreate(TaskFunction_t pxTaskCode,
                       const char * const pcName,
                       const configSTACK_DEPTH_TYPE uxStackDepth,
                       void * const pvParameters,
                       UBaseType_t uxPriority,
                       TaskHandle_t * const pxCreatedTask) {
    TCB_t pxNewTCB = __CPROVER_malloc(sizeof(tskTaskControlBlock));
    __CPROVER_assert(pxTaskCode != NULL, "Task code must not be NULL");

    if (pxNewTCB != NULL) {
        pxNewTCB->priority = uxPriority;
        pxNewTCB->pvParameters = pvParameters;
        *pxCreatedTask = pxNewTCB;
        return pdPASS;
    } else {
        return errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY;
    }
}

void vTaskStartScheduler(void) {
    __CPROVER_assume(0); // Scheduler should never return
}

// Simulate task yielding
void taskYIELD(TaskHandle_t currentTask, TaskHandle_t nextTask) {
    __CPROVER_assert(currentTask != NULL && nextTask != NULL, "Tasks must not be NULL");
    if (nextTask->priority > currentTask->priority) {
        currentTask->state = TASK_READY;
        nextTask->state = TASK_RUNNING;
    }
}

// Nondeterministic task function
void nondet_task_function(void *pvParameters) {
    while (1) {
        __CPROVER_assume(__CPROVER_nondet_bool());
    }
}

void CBMC_VerifyPreemption() {
    TaskHandle_t highPriorityTask = NULL;
    TaskHandle_t lowPriorityTask = NULL;

    // Create two tasks: one with higher priority and another with lower priority
    __CPROVER_assume(xTaskCreate(nondet_task_function, "HighPriorityTask", configMINIMAL_STACK_SIZE, NULL, 2, &highPriorityTask) == pdPASS);
    __CPROVER_assume(xTaskCreate(nondet_task_function, "LowPriorityTask", configMINIMAL_STACK_SIZE, NULL, 1, &lowPriorityTask) == pdPASS);

    // Assume the high-priority task is running
    highPriorityTask->state = TASK_RUNNING;
    lowPriorityTask->state = TASK_READY;

    // Simulate scheduler running
    taskYIELD(highPriorityTask, lowPriorityTask);

    // Assert that the lower-priority task does not preempt the high-priority task
    __CPROVER_assert(highPriorityTask->state == TASK_RUNNING, "High-priority task must continue running");
    __CPROVER_assert(lowPriorityTask->state != TASK_RUNNING, "Low-priority task must not preempt the high-priority task");
}
