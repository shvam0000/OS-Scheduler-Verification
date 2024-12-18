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
    UBaseType_t basePriority; // Base priority for inheritance tracking
} tskTaskControlBlock;

typedef tskTaskControlBlock* TaskHandle_t;

// Simulate dynamic memory allocation
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
        (*pxCreatedTask)->state = TASK_READY;
        (*pxCreatedTask)->priority = uxPriority;
        (*pxCreatedTask)->basePriority = uxPriority;
        return pdPASS;
    }
    return pdFAIL;
}

// Simulated mutex
typedef struct {
    TaskHandle_t owner; // Task that owns the mutex
} Mutex_t;

void xMutexTake(Mutex_t *mutex, TaskHandle_t task) {
    __CPROVER_assert(mutex != NULL && task != NULL, "Mutex and task must not be NULL");
    if (mutex->owner == NULL) {
        // Mutex is free, acquire it
        mutex->owner = task;
    } else {
        // Priority inheritance
        if (task->priority > mutex->owner->priority) {
            mutex->owner->priority = task->priority; // Inherit higher priority
        }
    }
}

void xMutexGive(Mutex_t *mutex, TaskHandle_t task) {
    __CPROVER_assert(mutex != NULL && task != NULL, "Mutex and task must not be NULL");
    __CPROVER_assert(mutex->owner == task, "Only the owner can release the mutex");
    mutex->owner->priority = mutex->owner->basePriority; // Restore base priority
    mutex->owner = NULL; // Release the mutex
}

// Scheduler simulation
void taskYIELD(TaskHandle_t currentTask, TaskHandle_t nextTask) {
    if (nextTask->priority > currentTask->priority) {
        currentTask->state = TASK_READY;
        nextTask->state = TASK_RUNNING;
    }
}

void nondet_task_function(void *pvParameters) {
    // Simulate a task function with an infinite loop and nondeterministic behavior
    while (1) {
        if (__CPROVER_nondet_bool()) {
            __CPROVER_assume(0); // Simulate some behavior
        }
    }
}


// Verification function for priority inheritance
void CBMC_VerifyPriorityInheritance() {
    TaskHandle_t highPriorityTask = NULL;
    TaskHandle_t lowPriorityTask = NULL;
    Mutex_t mutex = { NULL };

    // Explicitly assume pxTaskCode is not NULL
    TaskFunction_t validTaskFunction = nondet_task_function;

    // Create two tasks
    __CPROVER_assume(xTaskCreate(validTaskFunction, "HighPriorityTask", configMINIMAL_STACK_SIZE, NULL, 3, &highPriorityTask) == pdPASS);
    __CPROVER_assume(xTaskCreate(validTaskFunction, "LowPriorityTask", configMINIMAL_STACK_SIZE, NULL, 1, &lowPriorityTask) == pdPASS);

    // Low-priority task acquires the mutex
    xMutexTake(&mutex, lowPriorityTask);
    __CPROVER_assert(mutex.owner == lowPriorityTask, "Low-priority task must own the mutex");

    // High-priority task attempts to take the mutex
    xMutexTake(&mutex, highPriorityTask);

    // Verify priority inheritance
    __CPROVER_assert(lowPriorityTask->priority == highPriorityTask->priority, "Low-priority task must inherit high-priority task's priority");

    // Release the mutex
    xMutexGive(&mutex, lowPriorityTask);

    // Verify priority restoration
    __CPROVER_assert(lowPriorityTask->priority == lowPriorityTask->basePriority, "Low-priority task's priority must be restored after releasing the mutex");
}

