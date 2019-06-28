/**
  Project: Case study
  Version: 1.0
**/

// Include the header file that in turn will include all of the necessary FreeRTOS components.
#include "dependencies/world.h"

// Semaphore-handle creation.
static xSemaphoreHandle xSemaphoreCounter  = NULL;
static xSemaphoreHandle xSemaphoreSens0    = NULL;
static xSemaphoreHandle xSemaphoreSens1    = NULL;
static xSemaphoreHandle xSemaphoreComSens0 = NULL;
static xSemaphoreHandle xSemaphoreComSens1 = NULL;

static uint64_t counter;

/*@
    predicate counter_pred()    	
    	requires u_llong_integer(&counter, ?upval) &*& upval >= 0;
    predicate MEMORY_pred() = true;
    predicate ACCELEROMETER_pred() = true;
    predicate MEMORY_comm() = true;
    predicate ACCELEROMETER_comm() = true;
    predicate CHUNK(predicate() pred) = true;

    lemma void chunk_unfold();
    	requires CHUNK(?p);
    	ensures CHUNK(p) &*& p();

@*/

void system_init()
    /*@ requires
		u_llong_integer(&counter, _) &*&
		pointer(&xSemaphoreCounter, 0) &*&
		pointer(&xSemaphoreSens0, 0) &*&
		pointer(&xSemaphoreSens1, 0) &*&
		pointer(&xSemaphoreComSens0, 0) &*&
		pointer(&xSemaphoreComSens1, 0);
		@*/
    /*@ ensures
		pointer(&xSemaphoreCounter, ?semcounter) &*& sync_pred(semcounter, counter_pred, NULL) &*& queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, 1) &*&
    		pointer(&xSemaphoreSens0, ?mem) &*& sync_pred(mem, MEMORY_pred, NULL) &*& queue_pred(mem, queueQUEUE_TYPE_MUTEX, 1, 1) &*&
		pointer(&xSemaphoreSens1, ?accel) &*& sync_pred(accel, ACCELEROMETER_pred, NULL) &*& queue_pred(accel, queueQUEUE_TYPE_MUTEX, 1, 1) &*&
		pointer(&xSemaphoreComSens0, ?membinsem) &*& sync_pred(membinsem, MEMORY_comm, NULL) &*& queue_pred(membinsem, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, 0) &*&
		pointer(&xSemaphoreComSens1, ?accelbinsem) &*& sync_pred(accelbinsem, ACCELEROMETER_comm, NULL) &*&queue_pred(accelbinsem, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, 0); @*/
{
  counter = 0;
  /*@ close counter_pred(); @*/

  /*@ close sync_ghost_arg(counter_pred); @*/
  xSemaphoreCounter = xSemaphoreCreateMutex();
  if(xSemaphoreCounter == 0) abort();

  /*@ close MEMORY_pred(); @*/
  /*@ close sync_ghost_arg(MEMORY_pred); @*/
  xSemaphoreSens0 = xSemaphoreCreateMutex();
  if(xSemaphoreSens0 == 0) abort();

  /*@ close ACCELEROMETER_pred(); @*/
  /*@ close sync_ghost_arg(ACCELEROMETER_pred); @*/
  xSemaphoreSens1 = xSemaphoreCreateMutex();
  if(xSemaphoreSens1 == 0) abort();

  /*@ close MEMORY_comm(); @*/
  /*@ close sync_ghost_arg(MEMORY_comm); @*/
  xSemaphoreComSens0 = xSemaphoreCreateBinary();
  if(xSemaphoreComSens0 == 0) abort();
  /*@ initialize_binary_semaphore(xSemaphoreComSens0); @*/

  /*@ close ACCELEROMETER_comm(); @*/
  /*@ close sync_ghost_arg(ACCELEROMETER_comm); @*/
  xSemaphoreComSens1 = xSemaphoreCreateBinary();
  if(xSemaphoreComSens1 == 0) abort();
  /*@ initialize_binary_semaphore(xSemaphoreComSens1); @*/
}

uint64_t inspect_counter()
    /*@ requires
		[?f]running_task(?task) &*&
		[?f1]pointer(&xSemaphoreCounter, ?semcounter) &*& [?f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, ?cur) &*& [?f3]sync_pred(semcounter, counter_pred, ?holder); @*/
    /*@ ensures
		[f]running_task(task) &*&
		[f1]pointer(&xSemaphoreCounter, semcounter) &*& [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, 1) &*& [f3]sync_pred(semcounter, counter_pred, ?holder2); @*/
{
  uint64_t lcounter;
  /*@ open [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, cur); @*/
  /*@ close [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, cur); @*/

  xSemaphoreTake(xSemaphoreCounter, portMAX_DELAY);
  /*@ open counter_pred(); @*/
  lcounter = counter;
  /*@ close counter_pred(); @*/
  xSemaphoreGive(xSemaphoreCounter);

  return lcounter;
}

void increment_counter()
   /*@ requires
   		[?f]running_task(?task) &*&
   		[?f1]pointer(&xSemaphoreCounter, ?semcounter) &*& [?f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, ?cur) &*& [?f3]sync_pred(semcounter, counter_pred, ?holder); @*/
   /*@ ensures
		[f]running_task(task) &*&
		[f1]pointer(&xSemaphoreCounter, semcounter) &*& [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, 1) &*& [f3]sync_pred(semcounter, counter_pred, ?holder2); @*/
{
  // Open the queue predicate to add the size assumptions (cur <= max) to the list.
  /*@ open [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, cur); @*/
  /*@ close [f2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, cur); @*/

  xSemaphoreTake(xSemaphoreCounter, portMAX_DELAY);

  /*@ open counter_pred(); @*/
  if(counter == UINT64_MAX) abort();
  /*@ produce_limits(counter); @*/
  counter++;
  /*@ close counter_pred(); @*/
  xSemaphoreGive(xSemaphoreCounter);
}

int transfer_data(int node)
    /*@ requires
		[?f1]running_task(?task) &*&
		pointer(&xSemaphoreSens0, ?semsens0) &*& sync_pred(semsens0, MEMORY_pred, ?holder0) &*& queue_pred(semsens0, queueQUEUE_TYPE_MUTEX, 1, ?cur0) &*&
		pointer(&xSemaphoreSens1, ?semsens1) &*& sync_pred(semsens1, ACCELEROMETER_pred, ?holder2) &*& queue_pred(semsens1, queueQUEUE_TYPE_MUTEX, 1, ?cur2) &*&
		[?f2]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [?f3]sync_pred(semcomsens0, MEMORY_comm, ?holderint0) &*& [?f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint0) &*&
		[?f5]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [?f6]sync_pred(semcomsens1, ACCELEROMETER_comm, ?holderint2) &*& [?f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint2);
    	 @*/
    /*@ ensures
		[f1]running_task(task) &*&
		pointer(&xSemaphoreSens0, semsens0) &*& sync_pred(semsens0, MEMORY_pred, ?holder0new) &*& queue_pred(semsens0, queueQUEUE_TYPE_MUTEX, 1, ?cur0new) &*&
		pointer(&xSemaphoreSens1, semsens1) &*& sync_pred(semsens1, ACCELEROMETER_pred, ?holder2new) &*& queue_pred(semsens1, queueQUEUE_TYPE_MUTEX, 1, ?cur2new) &*&
		[f2]pointer(&xSemaphoreComSens0, semcomsens0) &*& [f3]sync_pred(semcomsens0, MEMORY_comm, ?holderint0new) &*& [f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint0new) &*&
		[f5]pointer(&xSemaphoreComSens1, semcomsens1) &*& [f6]sync_pred(semcomsens1, ACCELEROMETER_comm, ?holderint2new) &*& [f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint2new);
    	 @*/
{
  int ret;
  uint32_t          delay;
  xSemaphoreHandle  * Sem;
  xSemaphoreHandle  * BinSem;

  switch(node)
  {
    case MEMORY:
	/*@ open queue_pred(semsens0, queueQUEUE_TYPE_MUTEX, 1, cur0); @*/
	/*@ close queue_pred(semsens0, queueQUEUE_TYPE_MUTEX, 1, cur0); @*/
      Sem           = &xSemaphoreSens0;
	/*@ open [f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, curint0); @*/
	/*@ close [f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, curint0); @*/
      BinSem        = &xSemaphoreComSens0;
      break;

    case ACCELEROMETER:
	/*@ open queue_pred(semsens1, queueQUEUE_TYPE_MUTEX, 1, cur2); @*/
	/*@ close queue_pred(semsens1, queueQUEUE_TYPE_MUTEX, 1, cur2); @*/
      Sem           = &xSemaphoreSens1;
	/*@ open [f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, curint2); @*/
	/*@ close [f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, curint2); @*/
      BinSem        = &xSemaphoreComSens1;
      break;

    default:
      return FAILURE;
  }

  if (xSemaphoreTake( *Sem, (1000 / portTICK_RATE_MS)) != pdPASS)
  {
    /* The mutex could not be acquired within one second, indicating
       that the sensor is busy. Transfer attempt is terminated */
    return FAILURE;
  }

  /* Perform the transaction here. Determine a suitable delay
     in which the transfer should be able to complete. */
  delay = 3000;

  if (xSemaphoreTake( *BinSem, delay / portTICK_RATE_MS) != pdPASS)
  {
    /* The transfer was not able to finish in time. Report this to
       the caller so that appropriate action can be taken. */
    ret = FAILURE;
  }
  else {
    /* The transfer succesfully completed. */
    /*@ assert [_]pointer(BinSem, ?binsem) &*& [_]queue_pred(binsem, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, 0); @*/
    ret = SUCCESS;
  }

  /* Release the mutex and return the result */
  xSemaphoreGive( *Sem);

  /*@ assert [_]pointer(Sem, ?sem) &*& [_]queue_pred(sem, queueQUEUE_TYPE_MUTEX, 1, 1); @*/
  return ret;

}


void generate_transfer_interrupt(id_t * id)
    /*@ requires
		[?f1]running_task(?task) &*&
		[?f2]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [?f3]sync_pred(semcomsens0, MEMORY_comm, ?holderint0) &*& [?f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint0) &*&
		[?f5]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [?f6]sync_pred(semcomsens1, ACCELEROMETER_comm, ?holderint2) &*& [?f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint2);
	@*/
    /*@ ensures
		[f1]running_task(task) &*&
		[f2]pointer(&xSemaphoreComSens0, semcomsens0) &*& [f3]sync_pred(semcomsens0, MEMORY_comm, ?holderint0new) &*& [f4]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint0new) &*&
		[f5]pointer(&xSemaphoreComSens1, semcomsens1) &*& [f6]sync_pred(semcomsens1, ACCELEROMETER_comm, ?holderint2new) &*& [f7]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint2new);
	 @*/
{
  int i;
  xSemaphoreHandle  * BinSem;


  if (id == MEMBUS)
    {
      BinSem  = &xSemaphoreComSens0;
	/*@ close CHUNK(MEMORY_comm); @*/
    }
  else if (id == ACCELBUS)
    {
      BinSem  = &xSemaphoreComSens1;
	/*@ close CHUNK(ACCELEROMETER_comm); @*/
    }
  else
    return;

    /* Check if the transfer still needs to occur. */
    if (!transferHasOccurred(id))
    {
	/*@ chunk_unfold(); @*/
        /* Indicate that a transfer is pending. */
        xSemaphoreGive( *BinSem );
    }
    /*@ leak CHUNK(_); @*/
}


/*@ predicate_family_instance task_pre(vTaskMockCount)(void * params) =
	[1/2]pointer(&xSemaphoreCounter, ?semcounter) &*&
	[1/2]queue_pred(semcounter, queueQUEUE_TYPE_MUTEX, 1, ?cur) &*& [1/2]sync_pred(semcounter, counter_pred, ?holder) &*&
	[1/4]running_task(?task);
@*/

void vTaskMockCount( void * pvParameters ) /*@ : TaskFunction_t @*/
    /*@ requires task_pre(vTaskMockCount)(pvParameters); @*/
    /*@ ensures false; @*/
{
  uint64_t xCurrentCount;
  uint64_t xLastCount;
  const TickType_t xMaxDelay = 20;

  while(1) /*@
	invariant task_pre(vTaskMockCount)(pvParameters); @*/
  {
    /*@ open task_pre(vTaskMockCount)(pvParameters); @*/
    xCurrentCount = inspect_counter();


    if(xCurrentCount < xLastCount) abort();
    if((xCurrentCount - xLastCount) % 2 == 0) {
      increment_counter();
    }
    /*@ close task_pre(vTaskMockCount)(pvParameters); @*/
    xLastCount = xCurrentCount;
    vTaskDelay(rand() % xMaxDelay);
    }
}

/*@ predicate_family_instance task_pre(vTaskMockTransfer)(void * params) =
	[1/4]running_task(?task) &*&
	[1/2]pointer(&xSemaphoreComSens0, ?sem0) &*& [1/2]sync_pred(sem0, MEMORY_comm, ?holder0) &*& [1/2]queue_pred(sem0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?cur0) &*&
	[1/2]pointer(&xSemaphoreComSens1, ?sem1) &*& [1/2]sync_pred(sem1, ACCELEROMETER_comm, ?holder2) &*& [1/2]queue_pred(sem1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?cur2); @*/


void vTaskMockTransfer( void * pvParameters ) /*@ : TaskFunction_t @*/
    /*@ requires task_pre(vTaskMockTransfer)(pvParameters); @*/
    /*@ ensures false; @*/
{
  const TickType_t xMaxDelay = 15;

  while(1)
	/*@ invariant task_pre(vTaskMockTransfer)(pvParameters); @*/
  {
	/*@ open task_pre(vTaskMockTransfer)(pvParameters); @*/
	generate_transfer_interrupt(SPI0);
	generate_transfer_interrupt(SPI2);
	/*@ close task_pre(vTaskMockTransfer)(pvParameters); @*/

    	vTaskDelay(rand() % xMaxDelay);
  }
}

/*@ predicate_family_instance task_pre(vTaskMockTrigger)(void * params) =
	[1/4]running_task(?task) &*&
	pointer(&xSemaphoreSens0, ?semssens0) &*& sync_pred(semssens0, MEMORY_pred, ?holder0) &*& queue_pred(semssens0, queueQUEUE_TYPE_MUTEX, 1, ?cur0) &*&
	pointer(&xSemaphoreSens1, ?semssens1) &*& sync_pred(semssens1, ACCELEROMETER_pred, ?holder2) &*& queue_pred(semssens1, queueQUEUE_TYPE_MUTEX, 1, ?cur2) &*&
	[1/2]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [1/2]sync_pred(semcomsens0, MEMORY_comm, ?holderint0) &*& [1/2]queue_pred(semcomsens0, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint0) &*&
	[1/2]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [1/2]sync_pred(semcomsens1, ACCELEROMETER_comm, ?holderint2) &*& [1/2]queue_pred(semcomsens1, queueQUEUE_TYPE_BINARY_SEMAPHORE, 1, ?curint2); @*/



void vTaskMockTrigger( void * pvParameters ) /*@ : TaskFunction_t @*/
    /*@ requires task_pre(vTaskMockTrigger)(pvParameters); @*/
    /*@ ensures false; @*/
{
  const TickType_t xMaxDelay = 15;

  while(1)
	/*@ invariant task_pre(vTaskMockTrigger)(pvParameters); @*/
  {
	/*@ open task_pre(vTaskMockTrigger)(pvParameters); @*/
	transfer_data(ACCELEROMETER);
	transfer_data(MEMORY);
    	/*@ close task_pre(vTaskMockTrigger)(pvParameters); @*/
        vTaskDelay(rand() % xMaxDelay);
  }
}

void main()
    /*@ requires module(casestudy_annotated, true); @*/
    /*@ ensures false; @*/
{
    /*@ open_module(); @*/
    system_init();

    /*@ close running_task(NULL); @*/

    /*@ close task_pre(vTaskMockCount)(NULL); @*/
    xTaskCreate(vTaskMockCount, "CountMock_1", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockCount)(NULL); @*/
    xTaskCreate(vTaskMockCount, "CountMock_2", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockTransfer)(NULL); @*/
    xTaskCreate(vTaskMockTransfer, "MockTransfer", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockTrigger)(NULL); @*/
    xTaskCreate(vTaskMockTrigger, "MockTrigger", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    vTaskStartScheduler();
}
