

#ifndef __EverQuic_H
#define __EverQuic_H
#include "kremlin/internal/target.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>


#include "LowParse.h"
#include "EverQuic_Kremlib.h"
#include "EverQuic_EverCrypt.h"
#include "LowStar.h"

#define EverQuic_BInitial 0
#define EverQuic_BZeroRTT 1
#define EverQuic_BHandshake 2
#define EverQuic_BRetry 3

typedef uint8_t EverQuic_long_header_specifics_tags;

typedef struct EverQuic_long_header_specifics_s
{
  EverQuic_long_header_specifics_tags tag;
  union {
    struct 
    {
      uint8_t reserved_bits;
      uint64_t payload_and_pn_length;
      uint32_t packet_number_length;
      uint8_t *token;
      uint32_t token_length;
    }
    case_BInitial;
    struct 
    {
      uint8_t reserved_bits;
      uint64_t payload_and_pn_length;
      uint32_t packet_number_length;
    }
    case_BZeroRTT;
    struct 
    {
      uint8_t reserved_bits;
      uint64_t payload_and_pn_length;
      uint32_t packet_number_length;
    }
    case_BHandshake;
    struct 
    {
      uint8_t unused;
      uint8_t *odcid;
      uint32_t odcil;
    }
    case_BRetry;
  }
  ;
}
EverQuic_long_header_specifics;

#define EverQuic_BLong 0
#define EverQuic_BShort 1

typedef uint8_t EverQuic_header_tags;

typedef struct EverQuic_header_s
{
  EverQuic_header_tags tag;
  union {
    struct 
    {
      uint32_t version;
      uint8_t *dcid;
      uint32_t dcil;
      uint8_t *scid;
      uint32_t scil;
      EverQuic_long_header_specifics spec;
    }
    case_BLong;
    struct 
    {
      uint8_t reserved_bits;
      bool spin;
      uint8_t phase;
      uint8_t *cid;
      uint32_t cid_len;
      uint32_t packet_number_length;
    }
    case_BShort;
  }
  ;
}
EverQuic_header;

typedef struct EverQuic_result_s
{
  uint64_t pn;
  EverQuic_header header;
  uint32_t header_len;
  uint32_t plain_len;
  uint32_t total_len;
}
EverQuic_result;

typedef struct EverQuic_index_s
{
  Spec_Hash_Definitions_hash_alg hash_alg;
  Spec_Agile_AEAD_alg aead_alg;
}
EverQuic_index;

Spec_Hash_Definitions_hash_alg
EverQuic___proj__Mkindex__item__hash_alg(EverQuic_index projectee);

Spec_Agile_AEAD_alg EverQuic___proj__Mkindex__item__aead_alg(EverQuic_index projectee);

typedef struct EverQuic_state_s_s EverQuic_state_s;

bool EverQuic_uu___is_State(EverQuic_index i, EverQuic_state_s projectee);

Spec_Hash_Definitions_hash_alg
EverQuic___proj__State__item__the_hash_alg(EverQuic_index i, EverQuic_state_s projectee);

Spec_Agile_AEAD_alg
EverQuic___proj__State__item__the_aead_alg(EverQuic_index i, EverQuic_state_s projectee);

EverCrypt_AEAD_state_s
*EverQuic___proj__State__item__aead_state(EverQuic_index i, EverQuic_state_s projectee);

uint8_t *EverQuic___proj__State__item__iv(EverQuic_index i, EverQuic_state_s projectee);

uint8_t *EverQuic___proj__State__item__hp_key(EverQuic_index i, EverQuic_state_s projectee);

uint64_t *EverQuic___proj__State__item__pn(EverQuic_index i, EverQuic_state_s projectee);

EverCrypt_CTR_state_s
*EverQuic___proj__State__item__ctr_state(EverQuic_index i, EverQuic_state_s projectee);

Spec_Agile_AEAD_alg EverQuic_aead_alg_of_state(EverQuic_state_s *s);

Spec_Hash_Definitions_hash_alg EverQuic_hash_alg_of_state(EverQuic_state_s *s);

uint64_t EverQuic_last_packet_number_of_state(EverQuic_state_s *s);

EverCrypt_Error_error_code
EverQuic_create_in(
  EverQuic_index i,
  EverQuic_state_s **dst,
  uint64_t initial_pn,
  uint8_t *traffic_secret
);

EverCrypt_Error_error_code
EverQuic_encrypt(
  EverQuic_state_s *s,
  uint8_t *dst,
  uint64_t *dst_pn,
  EverQuic_header h,
  uint8_t *plain,
  uint32_t plain_len
);

void
EverQuic_initial_secrets(
  uint8_t *dst_client,
  uint8_t *dst_server,
  uint8_t *cid,
  uint32_t cid_len
);

EverCrypt_Error_error_code
EverQuic_decrypt(
  EverQuic_state_s *s,
  EverQuic_result *dst,
  uint8_t *packet,
  uint32_t len,
  uint8_t cid_len
);

bool EverQuic_uu___is_BInitial(EverQuic_long_header_specifics projectee);

uint8_t
EverQuic___proj__BInitial__item__reserved_bits(EverQuic_long_header_specifics projectee);

uint64_t
EverQuic___proj__BInitial__item__payload_and_pn_length(
  EverQuic_long_header_specifics projectee
);

uint32_t
EverQuic___proj__BInitial__item__packet_number_length(EverQuic_long_header_specifics projectee);

uint8_t *EverQuic___proj__BInitial__item__token(EverQuic_long_header_specifics projectee);

uint32_t
EverQuic___proj__BInitial__item__token_length(EverQuic_long_header_specifics projectee);

bool EverQuic_uu___is_BZeroRTT(EverQuic_long_header_specifics projectee);

uint8_t
EverQuic___proj__BZeroRTT__item__reserved_bits(EverQuic_long_header_specifics projectee);

uint64_t
EverQuic___proj__BZeroRTT__item__payload_and_pn_length(
  EverQuic_long_header_specifics projectee
);

uint32_t
EverQuic___proj__BZeroRTT__item__packet_number_length(EverQuic_long_header_specifics projectee);

bool EverQuic_uu___is_BHandshake(EverQuic_long_header_specifics projectee);

uint8_t
EverQuic___proj__BHandshake__item__reserved_bits(EverQuic_long_header_specifics projectee);

uint64_t
EverQuic___proj__BHandshake__item__payload_and_pn_length(
  EverQuic_long_header_specifics projectee
);

uint32_t
EverQuic___proj__BHandshake__item__packet_number_length(
  EverQuic_long_header_specifics projectee
);

bool EverQuic_uu___is_BRetry(EverQuic_long_header_specifics projectee);

uint8_t EverQuic___proj__BRetry__item__unused(EverQuic_long_header_specifics projectee);

uint8_t *EverQuic___proj__BRetry__item__odcid(EverQuic_long_header_specifics projectee);

uint32_t EverQuic___proj__BRetry__item__odcil(EverQuic_long_header_specifics projectee);

bool EverQuic_uu___is_BLong(EverQuic_header projectee);

uint32_t EverQuic___proj__BLong__item__version(EverQuic_header projectee);

uint8_t *EverQuic___proj__BLong__item__dcid(EverQuic_header projectee);

uint32_t EverQuic___proj__BLong__item__dcil(EverQuic_header projectee);

uint8_t *EverQuic___proj__BLong__item__scid(EverQuic_header projectee);

uint32_t EverQuic___proj__BLong__item__scil(EverQuic_header projectee);

EverQuic_long_header_specifics EverQuic___proj__BLong__item__spec(EverQuic_header projectee);

bool EverQuic_uu___is_BShort(EverQuic_header projectee);

uint8_t EverQuic___proj__BShort__item__reserved_bits(EverQuic_header projectee);

bool EverQuic___proj__BShort__item__spin(EverQuic_header projectee);

uint8_t EverQuic___proj__BShort__item__phase(EverQuic_header projectee);

uint8_t *EverQuic___proj__BShort__item__cid(EverQuic_header projectee);

uint32_t EverQuic___proj__BShort__item__cid_len(EverQuic_header projectee);

uint32_t EverQuic___proj__BShort__item__packet_number_length(EverQuic_header projectee);

uint32_t EverQuic_dcid_len(EverQuic_header h);

bool EverQuic_is_retry(EverQuic_header h);

uint32_t EverQuic_pn_length(EverQuic_header h);

bool EverQuic_has_payload_length(EverQuic_header h);

uint64_t EverQuic_payload_and_pn_length(EverQuic_header h);

uint64_t EverQuic_payload_length(EverQuic_header h);

uint32_t EverQuic_public_header_len(EverQuic_header h);

uint32_t EverQuic_header_len(EverQuic_header h);

uint64_t EverQuic___proj__Mkresult__item__pn(EverQuic_result projectee);

EverQuic_header EverQuic___proj__Mkresult__item__header(EverQuic_result projectee);

uint32_t EverQuic___proj__Mkresult__item__header_len(EverQuic_result projectee);

uint32_t EverQuic___proj__Mkresult__item__plain_len(EverQuic_result projectee);

uint32_t EverQuic___proj__Mkresult__item__total_len(EverQuic_result projectee);


#define __EverQuic_H_DEFINED
#endif
