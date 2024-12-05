#define configUSE_PREEMPTION 1
#define configUSE_16_BIT_TICKS 0
#define configMAX_PRIORITIES 5
#define configMINIMAL_STACK_SIZE 128
#define configTOTAL_HEAP_SIZE (10 * 1024)
#define configTICK_RATE_HZ 1000
#define configSYSTICK_CLOCK_HZ ( ( unsigned long ) 24000000 )