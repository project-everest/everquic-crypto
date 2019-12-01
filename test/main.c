#include <stdio.h>
#include <stdlib.h>

#include "EverQuic.h"

// Test data
// ---------

QUIC_Impl_index test_idx1 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_256,
  .aead_alg = Spec_Agile_AEAD_CHACHA20_POLY1305
};

QUIC_Impl_index test_idx2 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_384,
  .aead_alg = Spec_Agile_AEAD_AES128_GCM
};

QUIC_Impl_index test_idx3 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_512,
  .aead_alg = Spec_Agile_AEAD_AES256_GCM
};

static uint8_t test_traffic_secret[32U] = {
  0x48U, 0xc4U, 0x30U, 0x9bU, 0x5fU, 0x27U,
  0x52U, 0xe8U, 0x12U, 0x7bU, 0x01U, 0x66U,
  0x05U, 0x5aU, 0x9aU, 0x56U, 0xe5U, 0xf9U,
  0x06U, 0x31U, 0xe0U, 0x84U, 0x85U, 0xe0U,
  0xf8U, 0x9eU, 0x9cU, 0xecU, 0x4aU, 0xdeU,
  0xb6U, 0x50U
};

static uint8_t test_plain[10U] = {
  0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U
};

static uint32_t test_plain_len = (uint32_t)10U;

// Helpers
// -------

void LowStar_Printf_print_string (char * const str) {
  printf("%s", str);
}

bool QUICTest_is_success_body(EverCrypt_Error_error_code e)
{
  switch (e)
  {
    case EverCrypt_Error_UnsupportedAlgorithm:
      {
        LowStar_Printf_print_string("unsupported algorithm\n");
        return false;
      }
    case EverCrypt_Error_InvalidKey:
      {
        LowStar_Printf_print_string("invalid key\n");
        return false;
      }
    case EverCrypt_Error_AuthenticationFailure:
      {
        LowStar_Printf_print_string("auth failure\n");
        return false;
      }
    case EverCrypt_Error_InvalidIVLength:
      {
        LowStar_Printf_print_string("invalid IV length\n");
        return false;
      }
    case EverCrypt_Error_DecodeError:
      {
        LowStar_Printf_print_string("decode error\n");
        return false;
      }
    case EverCrypt_Error_Success:
      {
        LowStar_Printf_print_string("success\n");
        return true;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

bool QUICTest_check_is_true_body(bool e)
{
  if (e)
    LowStar_Printf_print_string("OK\n");
  else
    LowStar_Printf_print_string("KO\n");
  return e;
}

bool QUICTest_is_equal(char * const b1, char * const b2, uint32_t len) {
  return memcmp(b1, b2, len) == 0;
}

// Functional test (encrypt-decrypt roundtrip)
// -------------------------------------------

bool QUICTest_test(QUIC_Impl_index idx, uint8_t *plain, uint32_t plain_len)
{
  QUIC_Impl_state_s *st_enc = NULL;
  QUIC_Impl_state_s *st_dec = NULL;
  uint64_t initial_pn = (uint64_t)0U;
  uint8_t dcil8 = (uint8_t)20U;
  uint32_t dcil = (uint32_t)dcil8;
  uint8_t dcid[dcil];
  memset(dcid, 0U, dcil * sizeof dcid[0U]);
  uint32_t scil = (uint32_t)20U;
  uint8_t scid[scil];
  memset(scid, 0U, scil * sizeof scid[0U]);
  uint32_t token_len = (uint32_t)16U;
  uint8_t token[token_len];
  memset(token, 0U, token_len * sizeof token[0U]);
  uint32_t cipher_len = plain_len + (uint32_t)16U;
  QUIC_Impl_Base_long_header_specifics
  hdr_spec =
    {
      .tag = QUIC_Impl_Base_BInitial,
      {
        .case_BInitial = {
          .payload_length = (uint64_t)cipher_len,
          .packet_number_length = (uint32_t)3U,
          .token = token,
          .token_length = token_len
        }
      }
    };
  QUIC_Impl_Base_header
  hdr =
    {
      .tag = QUIC_Impl_Base_BLong,
      {
        .case_BLong = {
          .version = (uint32_t)0xff000017U, .dcid = dcid, .dcil = dcil, .scid = scid, .scil = scil,
          .spec = hdr_spec
        }
      }
    };
  uint32_t hdr_len = QUIC_Impl_header_len(hdr);
  uint32_t cipher_len1 = plain_len + (uint32_t)16U;
  uint32_t enc_dst_len = hdr_len + cipher_len1;
  uint8_t enc_dst[enc_dst_len];
  memset(enc_dst, 0U, enc_dst_len * sizeof enc_dst[0U]);
  uint64_t enc_dst_pn = initial_pn;
  QUIC_Impl_result
  dec_dst =
    {
      .pn = (uint64_t)0U, .header = hdr, .header_len = (uint32_t)0U, .plain_len = (uint32_t)0U,
      .total_len = (uint32_t)0U
    };
  EverCrypt_Error_error_code
  r = QUIC_Impl_create_in(idx, &st_enc, initial_pn, test_traffic_secret);
  LowStar_Printf_print_string("Performing ");
  LowStar_Printf_print_string("create_in st_enc");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_is_success_body(r))
    return false;
  QUIC_Impl_state_s *st_enc1 = st_enc;
  EverCrypt_Error_error_code
    r1 = QUIC_Impl_encrypt(st_enc1, enc_dst, &enc_dst_pn, hdr, plain, plain_len);
  LowStar_Printf_print_string("Performing ");
  LowStar_Printf_print_string("encrypt");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_is_success_body(r1))
    return false;
  uint64_t pn = enc_dst_pn;
  EverCrypt_Error_error_code
    r2 = QUIC_Impl_create_in(idx, &st_dec, initial_pn, test_traffic_secret);
  LowStar_Printf_print_string("Performing ");
  LowStar_Printf_print_string("create_in st_dec");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_is_success_body(r2))
    return false;
  QUIC_Impl_state_s *st_dec1 = st_dec;
  EverCrypt_Error_error_code
    r3 = QUIC_Impl_decrypt(st_dec1, &dec_dst, enc_dst, enc_dst_len, dcil8);
  LowStar_Printf_print_string("Performing ");
  LowStar_Printf_print_string("decrypt");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_is_success_body(r3))
    return false;
  QUIC_Impl_result res = dec_dst;
  LowStar_Printf_print_string("Checking ");
  LowStar_Printf_print_string("pn");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_check_is_true_body(res.pn == pn))
    return false;
  LowStar_Printf_print_string("Checking ");
  LowStar_Printf_print_string("header_len");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_check_is_true_body(res.header_len == hdr_len))
    return false;
  LowStar_Printf_print_string("Checking ");
  LowStar_Printf_print_string("plain_len");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_check_is_true_body(res.plain_len == plain_len))
    return false;
  LowStar_Printf_print_string("Checking ");
  LowStar_Printf_print_string("total_len");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_check_is_true_body(res.total_len == enc_dst_len))
    return false;
  uint8_t *plain_ = enc_dst + hdr_len;
  bool chk = QUICTest_is_equal(plain_, plain, plain_len);
  LowStar_Printf_print_string("Checking ");
  LowStar_Printf_print_string("plain");
  LowStar_Printf_print_string(": ");
  return QUICTest_check_is_true_body(chk);
}

int main () {
  if (QUICTest_test(test_idx1, test_plain, test_plain_len)) {
    printf("SUCCESS\n");
    return EXIT_SUCCESS;
  } else {
    printf("FAILURE\n");
    return EXIT_FAILURE;
  }
}
