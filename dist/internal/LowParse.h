

#ifndef __internal_LowParse_H
#define __internal_LowParse_H




#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
uint8_t LowParse_BitFields_get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi);

uint8_t LowParse_BitFields_set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v);

bool LowParse_Low_ErrorCode_is_error(uint64_t positionOrError);

#define LOWPARSE_LOW_ERRORCODE_VALIDATOR_ERROR_GENERIC ((uint64_t)4294967296U)

#define LOWPARSE_LOW_ERRORCODE_VALIDATOR_ERROR_NOT_ENOUGH_DATA ((uint64_t)8589934592U)

typedef struct LowParse_Slice_slice_s
{
  uint8_t *base;
  uint32_t len;
}
LowParse_Slice_slice;


#define __internal_LowParse_H_DEFINED
#endif
