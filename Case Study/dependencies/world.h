#ifndef __WORLD_H
#define __WORLD_H

#include "Structures.h"
#include "error.h"
#include <stdlib.h>

unsigned int rand();
    //@ requires true;
    //@ ensures true;
    
bool transferHasOccurred(id_t * id);
    //@ requires true;
    //@ ensures true;

/**  World Functions  **/
void system_init();

uint64_t inspect_counter();
void increment_counter();

int transfer_data(int sens);
void generate_transfer_interrupt(id_t * bus_id);

#endif  /* __WORLD_H */
/**  End of world.h  **/

