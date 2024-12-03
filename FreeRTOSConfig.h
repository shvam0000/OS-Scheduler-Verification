/* Define to 1 to use idle hook, 0 otherwise */
#define configUSE_IDLE_HOOK        0

/* Define to 1 to use tick hook, 0 otherwise */
#define configUSE_TICK_HOOK        0
#define configUSE_PREEMPTION 1
#define configUSE_16_BIT_TICKS 0
#define configMAX_PRIORITIES 5
#define configMINIMAL_STACK_SIZE 128
#define configTOTAL_HEAP_SIZE (10 * 1024)
#define configTICK_RATE_HZ 1000