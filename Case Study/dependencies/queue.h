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
predicate sync_pred(QueueHandle_t queue ; predicate() p, void * holder);
predicate queue_pred(QueueHandle_t *mechanism, unsigned char type, UBaseType_t uxMaxCount, UBaseType_t currentCount)
	requires currentCount <= uxMaxCount &*& currentCount >= 0;

lemma void initialize_binary_semaphore(QueueHandle_t hdl);
	requires queue_pred(hdl, ?type, ?max, ?cur) &*& 
		type == queueQUEUE_TYPE_BINARY_SEMAPHORE &*& 
		sync_ghost_arg(?p) &*& p();
	ensures queue_pred(hdl, type, max, cur) &*& sync_pred(hdl, p, NULL);
   
@*/

/*
 * Generic version of the queue creation function, which is in turn called by
 * any queue, semaphore or mutex creation function or macro.
 */
QueueHandle_t xQueueGenericCreate( const UBaseType_t uxQueueLength, const UBaseType_t uxItemSize, const uint8_t ucQueueType ); 
	/*@ requires uxQueueLength >= 0 &*& uxItemSize >= 0 &*&
		(ucQueueType == queueQUEUE_TYPE_BINARY_SEMAPHORE || ucQueueType == queueQUEUE_TYPE_MUTEX) ?
			uxQueueLength == 1 &*& uxItemSize == 0 
		:
			emp; @*/
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
    		[?f1]queue_pred(xQueue, ?type, ?max, ?cur) &*&
    		[?f2]sync_pred(xQueue, ?p, ?holder) &*& p(); @*/
    /*@ ensures 
    		[f]running_task(task) &*&
    		result == pdTRUE ?
			cur == 0 &*& [f1]queue_pred(xQueue, type, max, 1) &*& 
			[f2]sync_pred(xQueue, p, NULL) &*& 
			(type == queueQUEUE_TYPE_MUTEX ? 
				task == holder : true)
		:
	    		result == errQUEUE_FULL &*&
	    		[f1]queue_pred(xQueue, type, max, cur) &*&
	    		[f2]sync_pred(xQueue, p, holder) &*&
	    		(type == queueQUEUE_TYPE_MUTEX ? 
				p() &*& (cur == 0 ? 
					task != holder : cur == 1) 
			: 
				cur == max);

    @*/

/**
* Used for taking semaphores/mutexes
*/ 

BaseType_t xQueueGenericReceive( QueueHandle_t xQueue, void * pvBuffer, TickType_t xTicksToWait, const BaseType_t xJustPeek );
    /*@ requires 
		[?f]running_task(?task) &*&
		[?f1]queue_pred(xQueue, ?type, ?max, ?cur) &*&
		[?f2]sync_pred(xQueue, ?p, ?holder); @*/
    /*@ ensures 
    		[f]running_task(task) &*&
		(xTicksToWait == portMAX_DELAY || result == pdTRUE) ?
			result == pdTRUE &*& cur == 1 &*&
			holder == NULL &*& [f1]queue_pred(xQueue, type, max, 0) &*&
			[f2]sync_pred(xQueue, p, task) &*&
			(type == queueQUEUE_TYPE_MUTEX ? 
				p() : true)
		:
			result == pdFALSE &*& cur == 0 &*& [f1]queue_pred(xQueue, type, max, cur) &*&
			[f2]sync_pred(xQueue, p, holder);
    @*/

QueueHandle_t xQueueCreateMutex( const uint8_t ucQueueType ); 
    /*@ requires 
    		sync_ghost_arg(?p) &*&
    		p(); @*/
    /*@ ensures 
    		result != 0 ? 
			queue_pred(result, queueQUEUE_TYPE_MUTEX, 1, 1) &*&
			sync_pred(result, p, NULL)
		: 
			emp; @*/

#endif /* QUEUE_H */
