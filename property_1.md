# **Progress Report: CBMC Verification of Task Suspension in FreeRTOS**

## **Date: 8 December 2024**

Command to run:

```
cbmc scheduler_harness.c \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/include" \
    -I "/Users/shivamshekhar/Desktop/FreeRTOS-Kernel/portable/GCC/ARM_CM4F" \
    -DconfigUSE_IDLE_HOOK=0 \
    -DconfigUSE_TICK_HOOK=0 \
    -DconfigMAX_SYSCALL_INTERRUPT_PRIORITY=0 \
    -DconfigKERNEL_INTERRUPT_PRIORITY=0 \
    -DconfigPRIO_BITS=3 \
    --function CBMC_VerifySuspension
```

---

## **Overview**

This part of the project focuses on verifying the behavior of task suspension and resumption in FreeRTOS using CBMC. The verification ensures that tasks transition correctly between `READY`, `RUNNING`, and `SUSPENDED` states based on the corresponding API calls.

---

## **Implementation Details**

### **Key Components**

#### **1. Enhanced Task Data Structure**

- Introduced a simplified `tskTaskControlBlock` structure with:
  - A placeholder for the stack pointer (`pxStack`).
  - Task parameters (`pvParameters`).
  - Task state (`state`) represented by an enum:
    ```c
    typedef enum { TASK_READY, TASK_RUNNING, TASK_SUSPENDED } TaskState;
    ```

#### **2. Core FreeRTOS Stubs**

- **`xTaskCreate`**:
  - Simulates dynamic task creation using a static memory pool (`__CPROVER_malloc`).
  - Initializes task state to `TASK_READY`.
  - Returns `pdPASS` or `pdFAIL` based on memory availability.
- **`vTaskSuspend`**:
  - Changes the task state to `TASK_SUSPENDED`.
  - Includes assertions to validate non-NULL task handles.
- **`vTaskResume`**:

  - Changes the task state from `TASK_SUSPENDED` to `TASK_READY`.
  - Asserts the validity of task handles and ensures only suspended tasks are resumed.

- **`vTaskStartScheduler`**:
  - Models the scheduler's behavior with an infinite assumption (`__CPROVER_assume(0)`).

#### **3. Memory Allocation Simulation**

- Implemented `__CPROVER_malloc` with a static memory pool to simulate limited memory resources for task creation.

#### **4. Nondeterministic Task Behavior**

- Simulated task functions with `nondet_task_function`, which includes:
  - Infinite loops.
  - Nondeterministic behavior (`__CPROVER_nondet_bool`) to model real-world task variability.

---

### **Verification: `CBMC_VerifySuspension`**

#### **Functionality**

1. **Task Creation**:

   - Creates a task (`task1`) using `xTaskCreate`.
   - Ensures task creation succeeds with `__CPROVER_assume`.

2. **Task Suspension**:

   - Suspends the task using `vTaskSuspend`.
   - Verifies that the task's state transitions to `TASK_SUSPENDED`.

3. **Assertions**:
   - Ensures the task remains in `TASK_SUSPENDED` until explicitly resumed.
   - Validates that the task does not transition back to `READY` without a resumption API call.

---

## **Progress Summary**

### **Original State**

- Focused on basic task creation and scheduling.
- Lacked detailed modeling of task state transitions and API behavior.

### **Current Enhancements**

1. **Task State Management**:

   - Implemented `TASK_READY`, `TASK_RUNNING`, and `TASK_SUSPENDED` states.
   - Added explicit state transitions for `vTaskSuspend` and `vTaskResume`.

2. **Dynamic Memory Simulation**:

   - Used `__CPROVER_malloc` with a bounded memory pool to model FreeRTOS memory constraints.
   - Simulated out-of-memory conditions.

3. **Detailed Verification**:

   - Validated task state transitions during suspension and resumption.
   - Ensured tasks cannot transition back to `READY` without an explicit API call.

4. **Realistic Task Modeling**:
   - Included a nondeterministic task function to simulate unpredictable runtime behavior.

---

## **Key Outcomes**

1. **Verification Passed**:

   - Task state transitions (`READY` → `SUSPENDED`) were correctly modeled and verified.
   - Assertions ensured tasks remained suspended until explicitly resumed.

2. **Enhanced Realism**:

   - Simulated dynamic memory allocation and finite memory constraints.
   - Introduced nondeterministic task behavior for practical testing scenarios.

3. **Modularity**:
   - Modular stubs for task creation, suspension, and resumption improve scalability for future verification tasks.

---

## **Future Work**

1. Extend verification to include:

   - Task priority management.
   - Scheduler behavior for multiple tasks.
   - Interrupt handling during task suspension.

2. Simulate task preemption and context switching for more comprehensive modeling.

3. Introduce bounded loops in the scheduler for finite state analysis.

---

This progress demonstrates significant advancements in modeling and verifying task suspension and resumption in FreeRTOS, paving the way for deeper verification of scheduling and task management.
