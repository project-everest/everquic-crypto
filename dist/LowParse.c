

#include "internal/LowParse.h"

uint8_t LowParse_BitFields_get_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi)
{
  uint8_t op1 = (uint32_t)x << (8U - hi);
  return (uint32_t)op1 >> (8U - hi + lo);
}

uint8_t LowParse_BitFields_set_bitfield_gen8(uint8_t x, uint32_t lo, uint32_t hi, uint8_t v)
{
  uint8_t op0 = 255U;
  uint8_t op1 = (uint32_t)op0 >> (8U - (hi - lo));
  uint8_t op2 = (uint32_t)op1 << lo;
  uint8_t op3 = ~op2;
  uint8_t op4 = (uint32_t)x & (uint32_t)op3;
  uint8_t op5 = (uint32_t)v << lo;
  return (uint32_t)op4 | (uint32_t)op5;
}

#define VALIDATOR_MAX_LENGTH (4294967295ULL)

bool LowParse_Low_ErrorCode_is_error(uint64_t positionOrError)
{
  return positionOrError > VALIDATOR_MAX_LENGTH;
}

