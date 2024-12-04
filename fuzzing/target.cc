#include <stddef.h>
#include <stdint.h>

#include "tasks.h"

// Nondeterministic task function
void nondet_task_function(void *pvParameters) {
    for (;;) {
        if (nondet_bool()) {
            taskYIELD();
        } else {
            // Continue running
        }
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) 
{
	if (size < sizeof(configSTACK_DEPTH_TYPE) + sizeof(UBaseType_t))
		return 0;

	configSTACK_DEPTH_TYPE uxStackDepth;
	UBaseType_t uxPriority;	

	size_t idx = 0;
	memcpy(&uxStackDepth, &data[idx], sizeof(configSTACK_DEPTH_TYPE));
	idx += sizeof(configSTACK_DEPTH_TYPE);
	memcpy(&uxPriority, &data[idx], sizeof(UBaseType_t));
	idx += sizeof(UBaseType_t);

	/* Test xTaskCreate with fuzzed naming */
	xTaskCreate(nondet_task_function, &data[idx], uxStackDepth, NULL, uxPriority, NULL);

	/* Test xTaskCreate with fuzzed "parameters" */
	xTaskCreate(nondet_task_function, NULL, uxStackDepth, &data[idx], uxPriority, NULL);

}		
