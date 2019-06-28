#ifndef STRUCTURES_H
#define STRUCTURES_H

// Include necessary FreeRTOS components
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"
#include "peripherals.h"

typedef struct {
  // Abstracted
} SPI_Type;

/* SPI - Peripheral instance base addresses */
/** Peripheral SPI0 base address */
#define SPI0_BASE                                (0x10000000u)
/** Peripheral SPI0 base pointer */
#define SPI0                                     ((SPI_Type *)SPI0_BASE)
/** Peripheral SPI2 base address */
#define SPI2_BASE                                (0x20000000u)
/** Peripheral SPI2 base pointer */
#define SPI2                                     ((SPI_Type *)SPI2_BASE)

// ADDED STUFF BELOW FOR THE CASE STUDY ONLY
typedef SPI_Type id_t;

#endif // STRUCTURES_H
