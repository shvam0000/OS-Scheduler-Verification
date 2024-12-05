#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "FreeRTOS.h"
#include "task.h"
#include "FreeRTOSConfig.h"

// Nondeterministic task function
void nondet_task_function(void *pvParameters) {
    for (;;) {
	/* Spin */
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) 
{
	if (size < sizeof(configSTACK_DEPTH_TYPE) + sizeof(UBaseType_t))
		return 0;

	configSTACK_DEPTH_TYPE uxStackDepth;
	UBaseType_t uxPriority;	

	size_t idx = 0;
//	void *p = &uxStackDepth;
//	for (size_t i = 0; i < sizeof(configSTACK_DEPTH_TYPE); i++)
//	{
//		p[i] = data[idx];
//		idx++;
//	}
//
//	void *p = &uxPriority;
//	for (size_t i = 0; i < sizeof(UBaseType_t); i++)
//	{
//		p[i] = data[idx];
//		idx++;
//	}

	
	memcpy(&uxStackDepth, &data[idx], sizeof(configSTACK_DEPTH_TYPE));
	idx += sizeof(configSTACK_DEPTH_TYPE);
	memcpy(&uxPriority, &data[idx], sizeof(UBaseType_t));
	idx += sizeof(UBaseType_t);

	/* Test xTaskCreate with fuzzed naming */
	xTaskCreate(nondet_task_function, (char *) &data[idx], uxStackDepth, NULL, uxPriority, NULL);

	/* Test xTaskCreate with fuzzed "parameters" */
	xTaskCreate(nondet_task_function, NULL, uxStackDepth, (void *)&data[idx], uxPriority, NULL);
	return 0;

}		
