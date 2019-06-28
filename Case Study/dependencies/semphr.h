#ifndef SEMAPHORE_H
#define SEMAPHORE_H

#include "queue.h"
typedef QueueHandle_t SemaphoreHandle_t;

#define semBINARY_SEMAPHORE_QUEUE_LENGTH	( ( uint8_t ) 1U )
#define semSEMAPHORE_QUEUE_ITEM_LENGTH		( ( uint8_t ) 0U )
#define semGIVE_BLOCK_TIME			( ( uint32_t ) 0U )


#define xSemaphoreCreateBinary() xQueueGenericCreate( ( UBaseType_t ) 1, semSEMAPHORE_QUEUE_ITEM_LENGTH, queueQUEUE_TYPE_BINARY_SEMAPHORE )

#define xSemaphoreTake( xSemaphore, xBlockTime ) xQueueGenericReceive( ( QueueHandle_t ) ( xSemaphore ), NULL, ( xBlockTime ), pdFALSE )

#define xSemaphoreGive( xSemaphore ) xQueueGenericSend( ( QueueHandle_t ) ( xSemaphore ), NULL, semGIVE_BLOCK_TIME, queueSEND_TO_BACK )

#define xSemaphoreCreateMutex() xQueueCreateMutex( queueQUEUE_TYPE_MUTEX )

#endif /* SEMAPHORE_H */


