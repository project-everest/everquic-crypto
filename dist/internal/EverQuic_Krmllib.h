

#ifndef __internal_EverQuic_Krmllib_H
#define __internal_EverQuic_Krmllib_H

#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

static KRML_NOINLINE uint32_t FStar_UInt32_eq_mask(uint32_t a, uint32_t b);

static KRML_NOINLINE uint64_t FStar_UInt64_eq_mask(uint64_t a, uint64_t b);

static KRML_NOINLINE uint64_t FStar_UInt64_gte_mask(uint64_t a, uint64_t b);

static inline FStar_UInt128_uint128
FStar_UInt128_add_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

static inline FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t a);


#define __internal_EverQuic_Krmllib_H_DEFINED
#endif
