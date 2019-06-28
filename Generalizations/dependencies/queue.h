#ifndef QUEUE_H
#define QUEUE_H

#include "FreeRTOS.h"
#include "task.h"


/**
 * Type by which queues are referenced.  For example, a call to xQueueCreate()
 * returns an QueueHandle_t variable that can then be used as a parameter to
 * xQueueSend(), xQueueReceive(), etc.
 */
typedef void * QueueHandle_t;

/* For internal use only. */
#define	queueSEND_TO_BACK			( ( BaseType_t ) 0 )
#define	queueSEND_TO_FRONT			( ( BaseType_t ) 1 )
#define queueOVERWRITE				( ( BaseType_t ) 2 )

/* For internal use only.  These definitions *must* match those in queue.c. */
#define queueQUEUE_TYPE_BASE			( ( uint8_t ) 0U )
#define queueQUEUE_TYPE_SET			( ( uint8_t ) 0U )
#define queueQUEUE_TYPE_MUTEX 			( ( uint8_t ) 1U )
#define queueQUEUE_TYPE_COUNTING_SEMAPHORE	( ( uint8_t ) 2U )
#define queueQUEUE_TYPE_BINARY_SEMAPHORE	( ( uint8_t ) 3U )
#define queueQUEUE_TYPE_RECURSIVE_MUTEX		( ( uint8_t ) 4U )

/*@

// Synchronization mechanisms
predicate sync_ghost_arg(predicate() p) = true;
predicate ghost_type(const uint8_t type)
	requires 
		type == queueQUEUE_TYPE_MUTEX ||
		type == queueQUEUE_TYPE_BINARY_SEMAPHORE ||
		type == queueQUEUE_TYPE_COUNTING_SEMAPHORE; 

predicate queue_pred(QueueHandle_t *mechanism, unsigned char type, UBaseType_t uxMaxCount, UBaseType_t currentCount)
	requires currentCount <= uxMaxCount &*& currentCount >= 0;

predicate mutex_pred(QueueHandle_t queue, predicate() p, void * holder, UBaseType_t state) =
	queue_pred(queue, queueQUEUE_TYPE_MUTEX, 1, state);
predicate binsem_pred(QueueHandle_t queue, predicate() invar, UBaseType_t state) =
	queue_pred(queue, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, state);
predicate countingsem_pred(QueueHandle_t queue, predicate() invar, UBaseType_t size, UBaseType_t state) =
	queue_pred(queue, queueQUEUE_TYPE_COUNTING_SEMAPHORE, size, state);

lemma void initialize_binary_semaphore(QueueHandle_t hdl);
	requires queue_pred(hdl, ?type, ?max, ?cur) &*& sync_ghost_arg(?p) &*& p();
	ensures binsem_pred(hdl, p, 0);
   
@*/

/*
 * Generic version of the queue creation function, which is in turn called by
 * any queue, semaphore or mutex creation function or macro.
 */
QueueHandle_t xQueueGenericCreate( const UBaseType_t uxQueueLength, const UBaseType_t uxItemSize, const uint8_t ucQueueType );
	/*@ requires 
		uxQueueLength >= 0 &*& uxItemSize >= 0 &*&
		(ucQueueType == queueQUEUE_TYPE_BINARY_SEMAPHORE || 
		ucQueueType == queueQUEUE_TYPE_MUTEX) ?
			uxQueueLength == 1 &*& uxItemSize == 0 
		:	
			(ucQueueType == queueQUEUE_TYPE_COUNTING_SEMAPHORE ?
				uxQueueLength > 0 &*& uxItemSize == 0
			:
				emp); @*/
	/*@ ensures 
		result != 0 ? 
			queue_pred(result, ucQueueType, uxQueueLength, 0)
		: 
			emp;
   	@*/

/**
* Used for releasing semaphores/mutexes
*/

BaseType_t xQueueGenericSend( QueueHandle_t xQueue, const void * pvItemToQueue, TickType_t xTicksToWait, const BaseType_t xCopyPosition );
    /*@ requires 
    		[?f]running_task(?task) &*&
    		ghost_type(?type) &*&  
		type == queueQUEUE_TYPE_MUTEX ?
			[?f2]mutex_pred(xQueue, ?p, ?holder, ?state) &*& p() &*&
			ensures [f]running_task(task) &*& result == pdTRUE ?
				[f2]mutex_pred(xQueue, p, NULL, 1) &*& 
				task == holder
			:
				result == errQUEUE_FULL &*& 
				[f2]mutex_pred(xQueue, p, ?newholder, ?newstate) &*& p() &*&
				state == 0 ? task != holder : true
		:
			(type == queueQUEUE_TYPE_BINARY_SEMAPHORE ?			
				[?f2]binsem_pred(xQueue, ?inv, ?state) &*& inv() &*&
				ensures [f]running_task(task) &*& result == pdTRUE ? 
					[f2]binsem_pred(xQueue, inv, 1) 
				: 	 
					result == errQUEUE_FULL &*& 
					[f2]binsem_pred(xQueue, inv, ?newstate)
			:
				[?f2]countingsem_pred(xQueue, ?inv, ?size, ?state) &*& inv() &*&
				ensures [f]running_task(task) &*& result == pdTRUE ?
					state >= 0 &*& state <= size &*&
					[f2]countingsem_pred(xQueue, inv, size, state + 1)
				:
					result == errQUEUE_FULL &*&
					[f2]countingsem_pred(xQueue, inv, size, ?newsize));
    @*/
    /*@ ensures emp; @*/

/**
* Used for taking semaphores/mutexes
*/ 

BaseType_t xQueueGenericReceive( QueueHandle_t xQueue, void * pvBuffer, TickType_t xTicksToWait, const BaseType_t xJustPeek );
    /*@ requires 
		[?f]running_task(?task) &*&
		ghost_type(?type) &*&
		type == queueQUEUE_TYPE_MUTEX ?
			[?f2]mutex_pred(xQueue, ?p, ?holder, ?state) &*&
			ensures [f]running_task(task) &*& 
				(xTicksToWait == portMAX_DELAY || result == pdTRUE) ?
					result == pdTRUE &*&
					[f2]mutex_pred(xQueue, p, task, 0) &*& p()
				:
					result == pdFALSE &*&
					[f2]mutex_pred(xQueue, p, ?newholder, ?newstate)
		:
			(type == queueQUEUE_TYPE_BINARY_SEMAPHORE ? 
				[?f2]binsem_pred(xQueue, ?inv, ?state) &*&
				ensures	[f]running_task(task) &*& 
					(xTicksToWait == portMAX_DELAY || result == pdTRUE) ?
						result == pdTRUE &*&
						[f2]binsem_pred(xQueue, inv, 0)
					:
						result == pdFALSE &*&
						[f2]binsem_pred(xQueue, inv, ?newstate)
			:
				[?f2]countingsem_pred(xQueue, ?inv, ?size, ?state) &*&
				ensures [f]running_task(task) &*& 
					(xTicksToWait == portMAX_DELAY || result == pdTRUE) ?
						result == pdTRUE &*& state >= 0 &*& state <= size &*&
						[f2]countingsem_pred(xQueue, inv, size, state - 1) 
					:
						result == pdFALSE &*&
						[f2]countingsem_pred(xQueue, inv, size, ?newsize));
    @*/
    /*@ ensures emp; @*/

/*
 * For internal use only.  Use xSemaphoreCreateMutex(),
 * xSemaphoreCreateCounting() or xSemaphoreGetMutexHolder() instead of calling
 * these functions directly.
 */
QueueHandle_t xQueueCreateMutex( const uint8_t ucQueueType );
    /*@ requires 
    		sync_ghost_arg(?p) &*&
    		p(); @*/
    /*@ ensures 
    		result != 0 ? 
			mutex_pred(result, p, NULL, 1)
		: 
			emp; @*/

QueueHandle_t xQueueCreateCountingSemaphore( const UBaseType_t uxMaxCount, const UBaseType_t uxInitialCount );
    /*@ requires
    		uxMaxCount > 0 &*&
    		uxInitialCount >= 0 &*&
    		uxMaxCount >= uxInitialCount &*&
    		sync_ghost_arg(?inv) &*&
    		inv(); @*/
    /*@ ensures
    		result != 0 ?
    			countingsem_pred(result, inv, uxMaxCount, uxInitialCount)
    		:
    			emp; @*/
    

#endif /* QUEUE_H */
