#ifndef INC_TASK_H
#define INC_TASK_H

#include "FreeRTOS.h"


/**
 * task. h
 *
 * Type by which tasks are referenced.  For example, a call to xTaskCreate
 * returns (via a pointer parameter) an TaskHandle_t variable that can then
 * be used as a parameter to vTaskDelete to delete the task.
 *
 * \defgroup TaskHandle_t TaskHandle_t
 * \ingroup Tasks
 */
typedef void * TaskHandle_t;

/*
 * Used internally only.
 */
typedef struct xTIME_OUT
{
	BaseType_t xOverflowCount;
	TickType_t xTimeOnEntering;
} TimeOut_t;

/*
 * Defines the memory ranges allocated to the task when an MPU is used.
 */
typedef struct xMEMORY_REGION
{
	void *pvBaseAddress;
	uint32_t ulLengthInBytes;
	uint32_t ulParameters;
} MemoryRegion_t;

/**
 * task. h
 *
 * Macro to enable microcontroller interrupts.
 *
 * \defgroup taskENABLE_INTERRUPTS taskENABLE_INTERRUPTS
 * \ingroup SchedulerControl
 */
#define taskENABLE_INTERRUPTS()		portENABLE_INTERRUPTS()

/* Definitions returned by xTaskGetSchedulerState().  taskSCHEDULER_SUSPENDED is
0 to generate more optimal code when configASSERT() is defined as the constant
is used in assert() statements. */
#define taskSCHEDULER_SUSPENDED		( ( BaseType_t ) 0 )
#define taskSCHEDULER_NOT_STARTED	( ( BaseType_t ) 1 )
#define taskSCHEDULER_RUNNING		( ( BaseType_t ) 2 )

#define tskIDLE_PRIORITY		( ( UBaseType_t ) 0U )
    
/*@
	predicate_family task_pre(void * task)(void * data);	
	predicate task_ready(void * pxTaskCode)
		requires is_TaskFunction_t(pxTaskCode) == true;
	predicate running_task(void * task)
		requires task == 0 || is_TaskFunction_t(task) == true;
@*/

// Extracted from projdefs.h
typedef void TaskFunction_t( void * pvParameters );
	/*@ requires task_pre(this)(pvParameters); @*/
	/*@ ensures false; @*/
 

BaseType_t xTaskGenericCreate( TaskFunction_t * pxTaskCode, const char * pcName, const uint16_t usStackDepth, void * pvParameters, UBaseType_t uxPriority, TaskHandle_t * pxCreatedTask, StackType_t * puxStackBuffer, const MemoryRegion_t * xRegions );
	/*@ requires is_TaskFunction_t(pxTaskCode) == true &*& usStackDepth > 0 &*& uxPriority >= tskIDLE_PRIORITY &*& task_pre(pxTaskCode)(pvParameters); @*/
	/*@ ensures task_ready(pxTaskCode); @*/

#define xTaskCreate( pvTaskCode, pcName, usStackDepth, pvParameters, uxPriority, pxCreatedTask ) xTaskGenericCreate( ( pvTaskCode ), ( pcName ), ( usStackDepth ), ( pvParameters ), ( uxPriority ), ( pxCreatedTask ), ( NULL ), ( NULL ) )

void vTaskDelay( const TickType_t xTicksToDelay );
	/*@ requires true; @*/
	/*@ ensures true; @*/

void vTaskStartScheduler( void ); 
	/*@ requires true; @*/
	/*@ ensures false; @*/


#endif /* INC_TASK_H */



