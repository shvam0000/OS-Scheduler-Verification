#include "FreeRTOS.h"
#include "task.h"
#include "list.h"

//     Memory Safety property check (no task should get lost and all task should be assigned in their list): 
// 	- Create muliple tasks
// 	- while the harness is running, check if all the tasks are going in the appropriate list

// 	Counter example:
// 		- taskPriority2 either can go in taskPriority1' List
// 		OR
// 		- taskPriority2 gets lost and doesn't go in any list


// Mock definitions for CBMC
#define MAX_TASKS 10

typedef struct {
    UBaseType_t uxPriority;
    ListItem_t xStateListItem;
} TCB_t;


void harness() {
    TCB_t *tasks[MAX_TASKS];
    List_t readyList[MAX_TASKS];

    // Initialize task list and ready lists
    for (int i = 0; i < MAX_TASKS; i++) {
        __CPROVER_assume(i >= 0 && i < MAX_TASKS); // Prevent overflow and out of bounds access
        tasks[i] = malloc(sizeof(TCB_t));
        __CPROVER_assume(tasks[i] != NULL); // Ensure the pointer is non-NULL

        tasks[i]->uxPriority = i % configMAX_PRIORITIES; // Ensure valid access

        vListInitialise(&(readyList[tasks[i]->uxPriority])); // Initialize ready lists

        vListInsertEnd(&(readyList[tasks[i]->uxPriority]), &(tasks[i]->xStateListItem));
    }

    // Invariant check: All tasks must remain in their appropriate ready list
    for (int i = 0; i < MAX_TASKS; i++) {
        __CPROVER_assert(
            listIS_CONTAINED_WITHIN(&(readyList[tasks[i]->uxPriority]), &(tasks[i]->xStateListItem)),
            "Task not in correct ready list");
    }

    // Free tasks to clean up
    for (int i = 0; i < MAX_TASKS; i++) {
        free(tasks[i]);
    }
}
