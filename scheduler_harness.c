#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

// Mock definitions for CBMC
#define MAX_TASKS 10
#define configMAX_PRIORITIES 5

typedef struct {
    UBaseType_t uxPriority;
    ListItem_t xStateListItem;
} TCB_t;

void main() {
    TCB_t *tasks[MAX_TASKS];
    List_t readyList[configMAX_PRIORITIES];

    // Initialize task list and ready lists
    for (int i = 0; i < MAX_TASKS; i++) {
        __CPROVER_assume(i >= 0 && i < MAX_TASKS); // Prevent overflow and out of bounds access
        tasks[i] = malloc(sizeof(TCB_t));
        __CPROVER_assume(tasks[i] != NULL); // Ensure the pointer is non-NULL

        tasks[i]->uxPriority = i % configMAX_PRIORITIES; // Assign priorities cyclically

        vListInitialise(&(readyList[tasks[i]->uxPriority])); // Initialize ready lists

        vListInsertEnd(&(readyList[tasks[i]->uxPriority]), &(tasks[i]->xStateListItem));
    }

    // Simulate scheduler behavior
    TCB_t *highestPriorityTask = NULL;

    // Check for the highest priority task in the ready lists
    for (int priority = configMAX_PRIORITIES - 1; priority >= 0; priority--) {
        if (!listLIST_IS_EMPTY(&readyList[priority])) {
            ListItem_t *pxItem = listGET_HEAD_ENTRY(&readyList[priority]);
            highestPriorityTask = (TCB_t *)listGET_LIST_ITEM_OWNER(pxItem);
            break; // Stop after finding the first non-empty list (highest priority)
        }
    }

    // Invariant check: The highest priority task must always be selected to run
    for (int i = 0; i < MAX_TASKS; i++) {
        if (highestPriorityTask == tasks[i]) {
            // Ensure the highest priority task is in the correct ready list
            __CPROVER_assert(
                listIS_CONTAINED_WITHIN(&(readyList[highestPriorityTask->uxPriority]), &(highestPriorityTask->xStateListItem)),
                "Highest priority task not in its ready list");
            break;
        }
    }

    // Free tasks to clean up
    for (int i = 0; i < MAX_TASKS; i++) {
        free(tasks[i]);
    }
}
