/**
  Project: Case study
  Version: 1.0 - generalized specifications
**/

// Include the header file that in turn will include all of the necessary FreeRTOS components.
#include "dependencies/world.h"
#include <stdio.h>

// Semaphore-handle creation.
static xSemaphoreHandle xSemaphoreCounter  = NULL;
static xSemaphoreHandle xSemaphoreSens0    = NULL;
static xSemaphoreHandle xSemaphoreSens1    = NULL;
static xSemaphoreHandle xSemaphoreComSens0 = NULL;
static xSemaphoreHandle xSemaphoreComSens1 = NULL;
static xSemaphoreHandle xSemaphoreCounting = NULL;

static uint64_t counter;

/*@
    predicate counter_pred()
    	requires u_llong_integer(&counter, ?upval) &*& upval >= 0;

    predicate MEMORY_pred() = true;
    predicate ACCELEROMETER_pred() = true;
    predicate MEMORY_comm() = true;
    predicate ACCELEROMETER_comm() = true;
    predicate PRODCON() = true;
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
		pointer(&xSemaphoreComSens1, 0) &*&
		pointer(&xSemaphoreCounting, 0);
		@*/
    /*@ ensures
		pointer(&xSemaphoreCounter, ?semcounter) &*& mutex_pred(semcounter, counter_pred, NULL, 1) &*&
    		pointer(&xSemaphoreSens0, ?mem) &*& mutex_pred(mem, MEMORY_pred, NULL, 1) &*&
		pointer(&xSemaphoreSens1, ?accel) &*& mutex_pred(accel, ACCELEROMETER_pred, NULL, 1) &*&
		pointer(&xSemaphoreComSens0, ?membinsem) &*& binsem_pred(membinsem, MEMORY_comm, 0) &*&
		pointer(&xSemaphoreComSens1, ?accelbinsem) &*& binsem_pred(accelbinsem, ACCELEROMETER_comm, 0) &*&
		pointer(&xSemaphoreCounting, ?cnt) &*& countingsem_pred(cnt, PRODCON, _, _) ; @*/
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

  /*@ close PRODCON(); @*/
  /*@ close sync_ghost_arg(PRODCON); @*/
  xSemaphoreCounting = xSemaphoreCreateCounting(50, 0);
  if(xSemaphoreCounting == 0) abort();
  /*@ assert pointer(&xSemaphoreCounting, ?cnt) &*& countingsem_pred(cnt, PRODCON, 50, 0); @*/
 	
}

uint64_t inspect_counter()
    /*@ requires
		[?f]running_task(?task) &*&
		[?f1]pointer(&xSemaphoreCounter, ?semcounter) &*& [?f3]mutex_pred(semcounter, counter_pred, _, ?cur); @*/
    /*@ ensures
		[f]running_task(task) &*&
		[f1]pointer(&xSemaphoreCounter, semcounter) &*& [f3]mutex_pred(semcounter, counter_pred, _, 1); @*/
{
  uint64_t lcounter;
  
  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  xSemaphoreTake(xSemaphoreCounter, portMAX_DELAY);

  /*@ open counter_pred(); @*/
  lcounter = counter;
  /*@ close counter_pred(); @*/

  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  xSemaphoreGive(xSemaphoreCounter);

  return lcounter;
}

void increment_counter()
   /*@ requires
   		[?f]running_task(?task) &*&
   		[?f1]pointer(&xSemaphoreCounter, ?semcounter) &*& [?f3]mutex_pred(semcounter, counter_pred, _, ?cur); @*/
   /*@ ensures
		[f]running_task(task) &*&
		[f1]pointer(&xSemaphoreCounter, semcounter) &*& [f3]mutex_pred(semcounter, counter_pred, _, 1); @*/
{


  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  xSemaphoreTake(xSemaphoreCounter, portMAX_DELAY);

  /*@ open counter_pred(); @*/
  if(counter == UINT64_MAX) abort();
  /*@ produce_limits(counter); @*/
  counter++;
  /*@ close counter_pred(); @*/
  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  xSemaphoreGive(xSemaphoreCounter);
}

int transfer_data(int node)
    /*@ requires
		[?f1]running_task(?task) &*&
		pointer(&xSemaphoreSens0, ?semsens0) &*& mutex_pred(semsens0, MEMORY_pred, _, _) &*&
		pointer(&xSemaphoreSens1, ?semsens1) &*& mutex_pred(semsens1, ACCELEROMETER_pred, _, _) &*&
		[?f2]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [?f3]binsem_pred(semcomsens0, MEMORY_comm, _) &*&
		[?f5]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [?f6]binsem_pred(semcomsens1, ACCELEROMETER_comm, _);
    	 @*/
    /*@ ensures
		[f1]running_task(task) &*&
		pointer(&xSemaphoreSens0, semsens0) &*& mutex_pred(semsens0, MEMORY_pred, _, _) &*&
		pointer(&xSemaphoreSens1, semsens1) &*& mutex_pred(semsens1, ACCELEROMETER_pred, _, _) &*& 
		[f2]pointer(&xSemaphoreComSens0, semcomsens0) &*& [f3]binsem_pred(semcomsens0, MEMORY_comm, _) &*& 
		[f5]pointer(&xSemaphoreComSens1, semcomsens1) &*& [f6]binsem_pred(semcomsens1, ACCELEROMETER_comm, _);
    	 @*/
{
  int ret;
  uint32_t          delay;
  xSemaphoreHandle  * Sem;
  xSemaphoreHandle  * BinSem;

  switch(node)
  {
    case MEMORY:
      Sem           = &xSemaphoreSens0;
      BinSem        = &xSemaphoreComSens0;
      break;

    case ACCELEROMETER:
      Sem           = &xSemaphoreSens1;
      BinSem        = &xSemaphoreComSens1;
      break;

    default:
      return FAILURE;
  }
  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  if (xSemaphoreTake( *Sem, (1000 / portTICK_RATE_MS)) != pdPASS)
  {
    /* The mutex could not be acquired within one second, indicating
       that the sensor is busy. Transfer attempt is terminated */
    return FAILURE;
  }

  /* Perform the transaction here. Determine a suitable delay
     in which the transfer should be able to complete. */
  delay = 3000;
  
  /*@ close ghost_type(queueQUEUE_TYPE_BINARY_SEMAPHORE); @*/
  if (xSemaphoreTake( *BinSem, delay / portTICK_RATE_MS) != pdPASS)
  {
    /* The transfer was not able to finish in time. Report this to
       the caller so that appropriate action can be taken. */
    ret = FAILURE;
  }
  else {
    /* The transfer succesfully completed. */
    /*@ assert [_]pointer(BinSem, ?binsem) &*& [_]binsem_pred(binsem, _, 0); @*/
    ret = SUCCESS;
  }

  /* Release the mutex and return the result */
  
  /*@ close ghost_type(queueQUEUE_TYPE_MUTEX); @*/
  xSemaphoreGive( *Sem);

  /*@ assert [_]pointer(Sem, ?sem) &*& [_]mutex_pred(sem, _, NULL, 1); @*/
  return ret;

}


void generate_transfer_interrupt(id_t * id)
    /*@ requires
		[?f1]running_task(?task) &*&
		[?f2]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [?f3]binsem_pred(semcomsens0, MEMORY_comm, _) &*& 
		[?f5]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [?f6]binsem_pred(semcomsens1, ACCELEROMETER_comm, _);
	@*/
    /*@ ensures
		[f1]running_task(task) &*&
		[f2]pointer(&xSemaphoreComSens0, semcomsens0) &*& [f3]binsem_pred(semcomsens0, MEMORY_comm, _) &*& 
		[f5]pointer(&xSemaphoreComSens1, semcomsens1) &*& [f6]binsem_pred(semcomsens1, ACCELEROMETER_comm, _);
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
  	/*@ close ghost_type(queueQUEUE_TYPE_BINARY_SEMAPHORE); @*/
        xSemaphoreGive( *BinSem );
    }
    /*@ leak CHUNK(_); @*/
}
	

/*@ predicate_family_instance task_pre(vTaskMockCount)(void * params) =
	[_]pointer(&xSemaphoreCounter, ?semcounter) &*&
	[_]mutex_pred(semcounter, counter_pred, _, _) &*&
	[_]running_task(_);
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
	[_]running_task(_) &*&
	[_]pointer(&xSemaphoreComSens0, ?sem0) &*& [_]binsem_pred(sem0, MEMORY_comm, _) &*&
	[_]pointer(&xSemaphoreComSens1, ?sem1) &*& [_]binsem_pred(sem1, ACCELEROMETER_comm, _); @*/


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
	[_]running_task(_) &*&
	pointer(&xSemaphoreSens0, ?semssens0) &*& mutex_pred(semssens0, MEMORY_pred, _, _) &*&
	pointer(&xSemaphoreSens1, ?semssens1) &*& mutex_pred(semssens1, ACCELEROMETER_pred, _, _) &*&
	[_]pointer(&xSemaphoreComSens0, ?semcomsens0) &*& [_]binsem_pred(semcomsens0, MEMORY_comm, _) &*&
	[_]pointer(&xSemaphoreComSens1, ?semcomsens1) &*& [_]binsem_pred(semcomsens1, ACCELEROMETER_comm, _); @*/



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

/*@ predicate_family_instance task_pre(vTaskMockProducer)(void * params) =
	[_]running_task(_) &*& PRODCON() &*&
	[_]pointer(&xSemaphoreCounting, ?cnt) &*& [_]countingsem_pred(cnt, PRODCON, _, _); @*/

void vTaskMockProducer( void * pvParameters ) /*@ : TaskFunction_t @*/
    /*@ requires task_pre(vTaskMockProducer)(pvParameters); @*/
    /*@ ensures false; @*/
{

  const TickType_t xMaxDelay = 5;
  while(1)
	/*@ invariant task_pre(vTaskMockProducer)(pvParameters); @*/
  {
	/*@ open task_pre(vTaskMockProducer)(pvParameters); @*/
  	/*@ close ghost_type(queueQUEUE_TYPE_COUNTING_SEMAPHORE); @*/
	xSemaphoreGive(xSemaphoreCounting);
	/*@ close PRODCON(); @*/
    	/*@ close task_pre(vTaskMockProducer)(pvParameters); @*/
        vTaskDelay(rand() % xMaxDelay);
  }
}

/*@ predicate_family_instance task_pre(vTaskMockConsumer)(void * params) =
	[_]running_task(_) &*&
	[_]pointer(&xSemaphoreCounting, ?cnt) &*& [_]countingsem_pred(cnt, PRODCON, _, _); @*/

void vTaskMockConsumer( void * pvParameters ) /*@ : TaskFunction_t @*/
    /*@ requires task_pre(vTaskMockConsumer)(pvParameters); @*/
    /*@ ensures false; @*/
{

  int result;

  while(1)
	/*@ invariant task_pre(vTaskMockConsumer)(pvParameters); @*/
  {
	/*@ open task_pre(vTaskMockConsumer)(pvParameters); @*/

  	for(;;)
	/*@ requires [?f]running_task(?task) &*& [?f2]pointer(&xSemaphoreCounting, ?cnt) &*& [?f3]countingsem_pred(cnt, PRODCON, ?size, ?cnt1); @*/
	/*@ ensures [f]running_task(task) &*& [f2]pointer(&xSemaphoreCounting, cnt) &*& [f3]countingsem_pred(cnt, PRODCON, size, _); @*/	
	{
  		/*@ close ghost_type(queueQUEUE_TYPE_COUNTING_SEMAPHORE); @*/
  		result = xSemaphoreTake(xSemaphoreCounting, 0);
		if(result == pdTRUE) {
			printf("Consumed generated event.");
			/*@ assert [f3]countingsem_pred(cnt, PRODCON, size, cnt1 - 1); @*/
		} else {
			printf("Consumed all generated events, yielding...");
			break;
		}	
	}

	/*@ close task_pre(vTaskMockConsumer)(pvParameters); @*/
        vTaskDelay(1000);
  }
}

void main()
    /*@ requires module(casestudy_generalized, true); @*/
    /*@ ensures true; @*/
{
    /*@ open_module(); @*/
    system_init();

    /*@ close running_task(NULL); @*/

    /*@ leak
    		[_]running_task(NULL) &*&
    		[_]pointer(&xSemaphoreCounter, ?smcnt) &*& [_]mutex_pred(smcnt, counter_pred, NULL, _) &*&
    		[_]pointer(&xSemaphoreComSens0, ?sem0) &*& [_]binsem_pred(sem0, MEMORY_comm, _) &*&
    		[_]pointer(&xSemaphoreComSens1, ?sem1) &*& [_]binsem_pred(sem1, ACCELEROMETER_comm, _) &*&
    		[_]pointer(&xSemaphoreCounting, ?cnt) &*& [_]countingsem_pred(cnt, PRODCON, _, _);
    @*/
    		
    /*@ close task_pre(vTaskMockCount)(NULL); @*/
    xTaskCreate(vTaskMockCount, "CountMock_1", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockCount)(NULL); @*/
    xTaskCreate(vTaskMockCount, "CountMock_2", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockTransfer)(NULL); @*/
    xTaskCreate(vTaskMockTransfer, "MockTransfer", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockTrigger)(NULL); @*/
    xTaskCreate(vTaskMockTrigger, "MockTrigger", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close PRODCON(); @*/
    /*@ close task_pre(vTaskMockProducer)(NULL); @*/
    xTaskCreate(vTaskMockProducer, "MockProducer", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    /*@ close task_pre(vTaskMockConsumer)(NULL); @*/
    xTaskCreate(vTaskMockConsumer, "MockConsumer", 100, NULL, tskIDLE_PRIORITY + 4, NULL);

    vTaskStartScheduler();
}
