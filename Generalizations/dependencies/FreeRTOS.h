/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#ifndef INC_FREERTOS_H
#define INC_FREERTOS_H

/*
 * Include the generic headers required for the FreeRTOS port being used.
 */
#include <stddef.h>

/* Standard project definitions */
#include "projdefs.h"

/* Definitions specific to the port being used. */
#include "portable.h"

#include "FreeRTOSConfig.h"

/*
 * Check all the required application specific macros have been defined.
 * These macros are application specific and (as downloaded) are defined
 * within FreeRTOSConfig.h.
 */

#ifndef configUSE_RECURSIVE_MUTEXES
	#define configUSE_RECURSIVE_MUTEXES 0
#endif

#ifndef configUSE_MUTEXES
	#define configUSE_MUTEXES 0
#endif

#ifndef configUSE_COUNTING_SEMAPHORES
	#define configUSE_COUNTING_SEMAPHORES 0
#endif


/* Definitions to allow backward compatibility with FreeRTOS versions prior to
V8 if desired. */
#ifndef configENABLE_BACKWARD_COMPATIBILITY
	#define configENABLE_BACKWARD_COMPATIBILITY 1
#endif

#if configENABLE_BACKWARD_COMPATIBILITY == 1
	#define eTaskStateGet eTaskGetState
	#define portTickType TickType_t
	#define xTaskHandle TaskHandle_t
	#define xQueueHandle QueueHandle_t
	#define xSemaphoreHandle SemaphoreHandle_t
	#define xQueueSetHandle QueueSetHandle_t
	#define xQueueSetMemberHandle QueueSetMemberHandle_t
	#define xTimeOutType TimeOut_t
	#define xMemoryRegion MemoryRegion_t
	#define xTaskParameters TaskParameters_t
	#define xTaskStatusType	TaskStatus_t
	#define xTimerHandle TimerHandle_t
	#define xCoRoutineHandle CoRoutineHandle_t
	#define pdTASK_HOOK_CODE TaskHookFunction_t
	#define portTICK_RATE_MS portTICK_PERIOD_MS

	/* Backward compatibility within the scheduler code only - these definitions
	are not really required but are included for completeness. */
	#define tmrTIMER_CALLBACK TimerCallbackFunction_t
	#define pdTASK_CODE TaskFunction_t
	#define xListItem ListItem_t
	#define xList List_t
#endif /* configENABLE_BACKWARD_COMPATIBILITY */

#endif /* INC_FREERTOS_H */

