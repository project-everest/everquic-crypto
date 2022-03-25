

#ifndef __EverQuic_EverCrypt_H
#define __EverQuic_EverCrypt_H




#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
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

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

typedef uint8_t Spec_Agile_AEAD_alg;

#define Spec_Cipher_Expansion_Hacl_CHACHA20 0
#define Spec_Cipher_Expansion_Vale_AES128 1
#define Spec_Cipher_Expansion_Vale_AES256 2

typedef uint8_t Spec_Cipher_Expansion_impl;

#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5

typedef uint8_t EverCrypt_Error_error_code;

typedef struct EverCrypt_CTR_state_s_s EverCrypt_CTR_state_s;

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;


#define __EverQuic_EverCrypt_H_DEFINED
#endif
