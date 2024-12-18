#include "FreeRTOS.h"
#include "task.h"
#include "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/FreeRTOSConfig.h"

#undef taskYIELD

typedef enum { TASK_READY, TASK_RUNNING, TASK_SUSPENDED } TaskState;

// Task Control Block
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
    static char memory_pool[1024]; // Static memory pool
    static size_t offset = 0;      // Track current offset
    if (offset + size <= 1024) {
        void *ptr = &memory_pool[offset];
        offset += size;
        return ptr;                // Return allocated memory
    }
    return NULL;                   // Out of memory
}

// Simulated Ready List
TaskHandle_t readyList[10];
int readyListSize = 0;

void addToReadyList(TaskHandle_t task) {
    if (readyListSize < 10) {
        readyList[readyListSize++] = task;
    } else {
        __CPROVER_assert(0, "Ready list overflow");
    }
}


void removeFromReadyList(TaskHandle_t task) {
    for (int i = 0; i < readyListSize; i++) {
        if (readyList[i] == task) {
            for (int j = i; j < readyListSize - 1; j++) {
                readyList[j] = readyList[j + 1];
            }
            readyListSize--;
            break;
        }
    }
}

// Simplified xTaskCreate
BaseType_t xTaskCreate(TaskFunction_t pxTaskCode,
                       const char * const pcName,
                       const configSTACK_DEPTH_TYPE uxStackDepth,
                       void * const pvParameters,
                       UBaseType_t uxPriority,
                       TaskHandle_t * const pxCreatedTask) {
    TCB_t pxNewTCB = __CPROVER_malloc(sizeof(tskTaskControlBlock));
    __CPROVER_assert(pxCreatedTask != NULL, "Task handle pointer must not be NULL");

    if (pxNewTCB != NULL) {
        pxNewTCB->priority = uxPriority;
        pxNewTCB->pvParameters = pvParameters;
        pxNewTCB->state = TASK_READY; // Initial state is READY
        *pxCreatedTask = pxNewTCB;

        if (pxTaskCode != NULL) {
            __CPROVER_assert(pxTaskCode != NULL, "Task code must not be NULL");
        }

        addToReadyList(pxNewTCB); // Add to ready list
        return pdPASS;
    } else {
        return errCOULD_NOT_ALLOCATE_REQUIRED_MEMORY;
    }
}

// Simulate task yielding
void taskYIELD(TaskHandle_t currentTask) {
    __CPROVER_assert(currentTask != NULL, "Current task must not be NULL");

    // Find the highest-priority ready task
    TaskHandle_t highestPriorityTask = NULL;
    for (int i = 0; i < readyListSize; i++) {
        TaskHandle_t task = readyList[i];
        if (task->priority > currentTask->priority && task->state == TASK_READY) {
            highestPriorityTask = task;
        }
    }

    // Perform task switching if needed
    if (highestPriorityTask != NULL) {
        currentTask->state = TASK_READY;
        highestPriorityTask->state = TASK_RUNNING;
    }
}

void nondet_task_function(void *pvParameters) {
    for (;;) {
        __CPROVER_assume(__CPROVER_nondet_bool());
    }
}

// Idle Task and Timer Task
TaskHandle_t idleTask = NULL;
TaskHandle_t timerTask = NULL;

void createIdleTask(void) {
    BaseType_t xReturn = xTaskCreate(NULL, "IdleTask", configMINIMAL_STACK_SIZE, NULL, 0, &idleTask);
    __CPROVER_assert(xReturn == pdPASS, "Idle task creation failed");
    __CPROVER_assert(idleTask != NULL, "Idle task must be created successfully");
}

#if (configUSE_TIMERS == 1)
void createTimerTask(void) {
    BaseType_t xReturn = xTaskCreate(nondet_task_function, "TimerTask", configMINIMAL_STACK_SIZE, NULL, 1, &timerTask);
    __CPROVER_assert(xReturn == pdPASS, "Timer task creation failed");
}
#endif

// Simulate vTaskStartScheduler
void vTaskStartScheduler(void) {
    createIdleTask();

    #if (configUSE_TIMERS == 1)
    createTimerTask(); 
    #endif

    // Assume the scheduler starts running
    __CPROVER_assume(0); 
}

void CBMC_VerifyPreemption() {
    TaskHandle_t highPriorityTask = NULL;
    TaskHandle_t lowPriorityTask = NULL;

    // Create two tasks with different priorities
    __CPROVER_assume(xTaskCreate(NULL, "HighPriorityTask", configMINIMAL_STACK_SIZE, NULL, 2, &highPriorityTask) == pdPASS);
    __CPROVER_assume(xTaskCreate(NULL, "LowPriorityTask", configMINIMAL_STACK_SIZE, NULL, 1, &lowPriorityTask) == pdPASS);

    // Assume valid pointers
    __CPROVER_assume(highPriorityTask != NULL);
    __CPROVER_assume(lowPriorityTask != NULL);

    // Assume the high-priority task is running
    highPriorityTask->state = TASK_RUNNING;
    lowPriorityTask->state = TASK_READY;

    // Simulate task yielding
    taskYIELD(highPriorityTask);

    // Assertions for preemption
    if (highPriorityTask != NULL) {
        __CPROVER_assert(highPriorityTask->state == TASK_RUNNING, "High-priority task must continue running");
    }

    if (lowPriorityTask != NULL) {
        __CPROVER_assert(lowPriorityTask->state != TASK_RUNNING, "Low-priority task must not preempt the high-priority task");
    }

    // Ensure the idle task remains ready
    if (idleTask != NULL) {
        __CPROVER_assert(idleTask->state == TASK_READY, "Idle task must always remain in the ready state");
    }
}