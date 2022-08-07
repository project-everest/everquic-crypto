

#ifndef __EverQuic_EverCrypt_H
#define __EverQuic_EverCrypt_H




#include "krml/internal/target.h"
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7

typedef uint8_t Spec_Hash_Definitions_hash_alg;

typedef struct Prims_list__uint8_t_s Prims_list__uint8_t;

#define Prims_Nil 0
#define Prims_Cons 1

typedef uint8_t Prims_list__uint8_t_tags;

typedef struct Prims_list__uint8_t_s
{
  Prims_list__uint8_t_tags tag;
  uint8_t hd;
  Prims_list__uint8_t *tl;
}
Prims_list__uint8_t;

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

typedef uint8_t Spec_Agile_AEAD_alg;

#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5

typedef uint8_t EverCrypt_Error_error_code;


#define __EverQuic_EverCrypt_H_DEFINED
#endif
