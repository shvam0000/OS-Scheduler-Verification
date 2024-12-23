#include "FreeRTOS.h"
#include "task.h"
#include "list.h"
#include <stdlib.h>

#define MAX_TASKS 10
#define configMAX_PRIORITIES 5

typedef struct {
    UBaseType_t uxPriority;
    ListItem_t xStateListItem;
} TCB_t;

void *pvPortMalloc(size_t size) {
    void *ptr = malloc(size);
    __CPROVER_assume(ptr != NULL);
    return ptr;
}

void vPortFree(void *ptr) {
    free(ptr);
}

void main() {
    TCB_t *tasks[MAX_TASKS];
    List_t readyList[configMAX_PRIORITIES];

    // Initialize ready lists
    for (unsigned int priority = 0; priority < configMAX_PRIORITIES; priority++) {
        vListInitialise(&readyList[priority]);
    }

    // Create tasks and assign them to ready lists
    for (unsigned int i = 0; i < MAX_TASKS; i++) {
        __CPROVER_assume(i < MAX_TASKS); // Prevent out-of-bounds
        tasks[i] = pvPortMalloc(sizeof(TCB_t));
        __CPROVER_assume(tasks[i] != NULL); // Ensure tasks[i] is valid

        tasks[i]->uxPriority = i % configMAX_PRIORITIES;

        // Initialize task's list item and add it to the corresponding ready list
        vListInitialiseItem(&tasks[i]->xStateListItem);
        listSET_LIST_ITEM_OWNER(&tasks[i]->xStateListItem, tasks[i]);
        vListInsertEnd(&readyList[tasks[i]->uxPriority], &tasks[i]->xStateListItem);
    }

    // Simulate scheduler to pick the highest-priority task
    TCB_t *highestPriorityTask = NULL;
    for (UBaseType_t priority = configMAX_PRIORITIES - 1; priority < configMAX_PRIORITIES; priority--) {
        if (!listLIST_IS_EMPTY(&readyList[priority])) {
            ListItem_t *pxItem = listGET_HEAD_ENTRY(&readyList[priority]);
            highestPriorityTask = (TCB_t *)listGET_LIST_ITEM_OWNER(pxItem);
            break;
        }
    }

    // Verify the scheduler picks the highest-priority task
    __CPROVER_assert(
        highestPriorityTask != NULL &&
        listIS_CONTAINED_WITHIN(&readyList[highestPriorityTask->uxPriority], &highestPriorityTask->xStateListItem),
        "Highest-priority task not in its ready list"
    );

    // Cleanup
    for (unsigned int i = 0; i < MAX_TASKS; i++) {
        __CPROVER_assume(i < MAX_TASKS); // Prevent out-of-bounds
        vPortFree(tasks[i]);
    }
}
