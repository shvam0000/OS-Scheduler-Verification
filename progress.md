Date - 2 December 2024

### **Original State**

#### Command to run -

```
cbmc scheduler_harness.c \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/include" \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/portable/GCC/ARM_CM4F" \
    -DconfigUSE_IDLE_HOOK=0 \
    -DconfigUSE_TICK_HOOK=0 \
    -DconfigMAX_SYSCALL_INTERRUPT_PRIORITY=0 \
    -DconfigKERNEL_INTERRUPT_PRIORITY=0 \
    -DconfigPRIO_BITS=3 \
    --function CBMC_RunScheduler
```

#### `scheduler_example.c`

- **Functionality**:
  - Contained two task definitions (`task1` and `task2`) that implemented infinite loops.
  - Included a minimal `CBMC_RunScheduler` function to:
    - Create two tasks using `xTaskCreate`.
    - Start the scheduler with `vTaskStartScheduler`.
    - Assert that the scheduler never returns.
- **Stubs**:
  - `xTaskCreate` and `vTaskStartScheduler` were minimal:
    - Did not simulate dynamic memory or task handles.
    - Always assumed success without verifying conditions.

#### `scheduler_harness.c`

- **Functionality**:
  - Focused on calling `CBMC_RunScheduler` with minimal logic.
- **Limitations**:
  - Tasks were initialized and started without detailed validation.
  - Lacked implementations for critical FreeRTOS constructs (e.g., task handles, memory management).
  - No modular handling of verification logic (e.g., task creation success or failures, dynamic memory allocation).

---

### **Current State**

#### `scheduler_example.c` Enhancements

1. **Dynamic Task Handle Management**:

   - Task creation now uses task handles (`TaskHandle_t`), enabling verification of memory allocation and task validity.

2. **Improved Stubs**:

   - `xTaskCreate`:
     - Uses `__CPROVER_malloc` to simulate task handle allocation.
     - Adds verification for pointer validity.
   - `vTaskStartScheduler`:
     - Includes `__CPROVER_assume(0)` to model the scheduler's non-returning behavior.

3. **Nondeterministic Logic**:
   - Tasks now include nondeterministic behavior using `nondet_bool`.

#### `scheduler_harness.c` Enhancements

1. **Detailed Verification Logic**:

   - Assertions added to validate successful task creation (`xTask1Handle` and `xTask2Handle`).
   - Explicit checks ensure the scheduler never returns.

2. **Dynamic Memory Allocation**:

   - Implemented `__CPROVER_malloc` to simulate dynamic memory allocation.
   - Uses a static memory pool for bounded analysis.

3. **Task Yielding**:

   - Introduced `taskYIELD` as a stub to model FreeRTOS's task yielding mechanism.

4. **Modular Stubs**:

   - Refactored stubs for clarity and modularity:
     - Task function definitions.
     - `xTaskCreate`.
     - `vTaskStartScheduler`.

5. **Handling Macros**:
   - Resolved conflicts with the `taskYIELD` macro defined in FreeRTOS headers by using `#undef taskYIELD`.

---

### **Key Improvements**

1. **Increased Realism**:

   - Models dynamic task management (handles and memory) closer to real FreeRTOS behavior.
   - Task functions and scheduler logic include realistic stubs to simulate actual runtime behavior.

2. **Enhanced Verification**:

   - Expanded assertions to ensure tasks are created successfully.
   - Explicit checks validate scheduler behavior (e.g., never returning).

3. **Support for CBMC Verification**:

   - Leverages `__CPROVER_malloc`, `__CPROVER_assert`, and `__CPROVER_assume` for bounded model checking.
   - Modular stubs and task function definitions simplify extension and verification.

4. **Conflict Resolution**:
   - Macro conflicts (e.g., `taskYIELD`) resolved using `#undef`.

---

### **Progression**

#### Original Focus

- Provided a basic setup for testing the scheduler.
- Lacked detailed modeling or realistic task management.

#### Current Focus

- Comprehensive harness and example with:
  - Realistic task creation and memory simulation.
  - Modular, conflict-free code.
  - Detailed assertions for verifying scheduler behavior.
- Ready for deeper CBMC verification tasks like proving liveness, safety, and scheduling properties.

---

This documentation outlines the project's progress and enhancements, emphasizing modularity, realism, and verification readiness.
