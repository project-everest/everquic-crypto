

#ifndef __internal_LowStar_H
#define __internal_LowStar_H

#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

static inline void store128_le(uint8_t *x0, FStar_UInt128_uint128 x1);

static inline FStar_UInt128_uint128 load128_be(uint8_t *x0);

extern void LowStar_Printf_print_string(Prims_string uu___);


#define __internal_LowStar_H_DEFINED
#endif
