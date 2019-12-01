#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>

#include "timing.h"

#define EVERCRYPT_TARGETCONFIG_X64 1
#include "EverQuic.h"

// Timing infrastructure
// ---------------------
//
// This code runs a given benchmark twice. First, for a set duration, to measure
// throughput. Second, for a given number of iterations, to measure cycles per
// byte.

// How long to measure for KB/s figures
#define MEASUREMENT_TIME 2
// How many iterations to run for cycles/byte figures
#define ITERATIONS(bsize) 1
#define HEADER_FORMAT   "  %s, fragment size=%d:  "

#define TIME_AND_TSC( TITLE, FRAG, BUFSIZE, CODE )                      \
do {                                                                    \
    uint64_t ii, jj, tsc;                                               \
    uint64_t cnt = ITERATIONS(BUFSIZE);                                 \
                                                                        \
    printf( HEADER_FORMAT, TITLE, FRAG );                               \
    fflush( stdout );                                                   \
                                                                        \
    set_alarm( MEASUREMENT_TIME );                                      \
    for( ii = 1; ! timing_alarmed; ii++ )                               \
    {                                                                   \
        CODE;                                                           \
    }                                                                   \
                                                                        \
    tsc = timing_hardclock();                                           \
    for( jj = 0; jj < cnt; jj++ )                                       \
    {                                                                   \
        CODE;                                                           \
    }                                                                   \
                                                                        \
    printf( "%9lu KiB/s,  %9f cycles/byte\n",                           \
                     (ii * BUFSIZE) / (MEASUREMENT_TIME * 1024),        \
                     (double)(timing_hardclock() - tsc ) /(double)( jj * BUFSIZE ) ); \
} while( 0 )


// Test data
// ---------

QUIC_Impl_index test_idx1 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_256,
  .aead_alg = Spec_Agile_AEAD_CHACHA20_POLY1305
};

QUIC_Impl_index test_idx2 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_256,
  .aead_alg = Spec_Agile_AEAD_AES128_GCM
};

QUIC_Impl_index test_idx3 = {
  .hash_alg = Spec_Hash_Definitions_SHA2_384,
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
        //LowStar_Printf_print_string("success\n");
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

bool QUICTest_is_equal(uint8_t *b1, uint8_t *b2, uint32_t len) {
  return memcmp(b1, b2, len) == 0;
}

// Functional test (encrypt-decrypt roundtrip)
// -------------------------------------------

bool QUICTest_test_core(QUIC_Impl_index idx, uint8_t *plain, uint32_t plain_len,
  uint64_t initial_pn, uint8_t *dcid, uint32_t dcil, uint8_t *scid, uint32_t scil,
  uint8_t *token, uint32_t token_len, bool debug)
{
  uint8_t dcil8 = dcil;
  uint32_t cipher_len = plain_len + 16;
  QUIC_Impl_state_s *st_enc = NULL;
  QUIC_Impl_state_s *st_dec = NULL;
  QUIC_Impl_Base_long_header_specifics hdr_spec = {
    .tag = QUIC_Impl_Base_BInitial,
    {
      .case_BInitial = {
        .payload_length = (uint64_t)cipher_len,
        .packet_number_length = (uint32_t)4U,
        .token = token,
        .token_length = token_len
      }
    }
  };
  QUIC_Impl_Base_header hdr = {
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
  QUIC_Impl_result dec_dst = {
    .pn = (uint64_t)0U, .header = hdr, .header_len = (uint32_t)0U, .plain_len = (uint32_t)0U,
    .total_len = (uint32_t)0U
  };
  EverCrypt_Error_error_code r =
    QUIC_Impl_create_in(idx, &st_enc, initial_pn, test_traffic_secret);
  if (debug)
    LowStar_Printf_print_string("Performing create_in st_enc : ");
  if (!QUICTest_is_success_body(r))
    return false;
  QUIC_Impl_state_s *st_enc1 = st_enc;
  EverCrypt_Error_error_code r1 =
    QUIC_Impl_encrypt(st_enc1, enc_dst, &enc_dst_pn, hdr, plain, plain_len);
  if (debug)
    LowStar_Printf_print_string("Performing encrypt : ");
  if (!QUICTest_is_success_body(r1))
    return false;
  uint64_t pn = enc_dst_pn;
  EverCrypt_Error_error_code
    r2 = QUIC_Impl_create_in(idx, &st_dec, initial_pn, test_traffic_secret);
  if (debug)
    LowStar_Printf_print_string("Performing create_in st_dec : ");
  if (!QUICTest_is_success_body(r2))
    return false;
  QUIC_Impl_state_s *st_dec1 = st_dec;
  EverCrypt_Error_error_code
    r3 = QUIC_Impl_decrypt(st_dec1, &dec_dst, enc_dst, enc_dst_len, dcil8);
  if (debug)
    LowStar_Printf_print_string("Performing decrypt : ");
  if (!QUICTest_is_success_body(r3))
    return false;
  QUIC_Impl_result res = dec_dst;
  if (debug)
    LowStar_Printf_print_string("Checking pn : ");
  if (!(res.pn == pn))
    return false;
  if (debug)
    LowStar_Printf_print_string("Checking header_len : ");
  if (!(res.header_len == hdr_len))
    return false;
  if (debug)
    LowStar_Printf_print_string("Checking plain_len : ");
  if (!(res.plain_len == plain_len))
    return false;
  if (debug)
    LowStar_Printf_print_string("Checking total_len : ");
  if (!(res.total_len == enc_dst_len))
    return false;
  uint8_t *plain_ = enc_dst + hdr_len;
  bool chk = QUICTest_is_equal(plain_, plain, plain_len);
  if (debug)
    LowStar_Printf_print_string("Checking plain : ");
  return chk;
}

bool QUICTest_test(QUIC_Impl_index idx, uint8_t *plain, uint32_t plain_len) {
  uint64_t initial_pn = 0U;
  uint32_t dcil = 20;
  uint8_t dcid[20] = { 0 };
  uint32_t scil = 20;
  uint8_t scid[20] = { 0 };
  uint32_t token_len = 16;
  uint8_t token[16] = { 0 };
  return QUICTest_test_core(idx, plain, plain_len, initial_pn, dcid, dcil, scid, scil,
    token, token_len, true);
}

static uint32_t fragment_sizes[] = {
  16, 32, 64, 128, 256, 512, 1024, 1300, 0
};

void QUICTest_benchmark0(QUIC_Impl_state_s *st_enc, uint8_t *plain, uint32_t plain_len,
  uint64_t initial_pn, uint8_t *dcid, uint32_t dcil, uint8_t *scid, uint32_t scil,
  uint8_t *token, uint32_t token_len, uint32_t fragment)
{
  uint32_t rem = plain_len;
  uint8_t out[1400];
 
  QUIC_Impl_Base_long_header_specifics hdr_spec = {
    .tag = QUIC_Impl_Base_BInitial,
    {
      .case_BInitial = {
        .payload_length = (uint64_t)fragment,
        .packet_number_length = (uint32_t)4U,
        .token = token,
        .token_length = token_len
      }
    }
  };
  QUIC_Impl_Base_header hdr = {
    .tag = QUIC_Impl_Base_BLong,
    {
      .case_BLong = {
        .version = (uint32_t)0xff000017U, .dcid = dcid, .dcil = dcil, .scid = scid, .scil = scil,
        .spec = hdr_spec
      }
    }
  };


  while (rem > 0) {
    uint32_t sz = rem >= fragment ? fragment : rem;
    EverCrypt_Error_error_code ret = QUIC_Impl_encrypt(st_enc, out, &initial_pn, hdr, plain, sz);
    if (!QUICTest_is_success_body(ret))
      exit(4);
    rem -= sz;
    plain += sz;
  }
}

void QUICTest_benchmark() {
  // Dummies.
  uint64_t initial_pn = 0U;
  uint32_t dcil = 20;
  uint8_t dcid[20] = { 0 };
  uint32_t scil = 20;
  uint8_t scid[20] = { 0 };
  uint32_t token_len = 16;
  uint8_t token[16] = { 0 };

  uint32_t plain_len = 1*1024*1024;
  uint8_t *plain = malloc(plain_len);

  /*
  printf("Reading 1M of random data...\n");
  int fd = open("./random", O_RDONLY);
  if (fd == -1){
	 printf("Can't read file");
    exit(1);
  }
  uint64_t res = read(fd, plain, plain_len);
  if (res != plain_len)
  {
	  printf("Read failed: %d\n", res);
    exit(2);
  }
  close(fd);
  printf("...read 1M of random data\n");
  */

  /*
  for (uint32_t i = 0; fragment_sizes[i] != 0; ++i) {
    uint32_t f = fragment_sizes[i];
    TIME_AND_TSC("1M encrypt/decrypt CHACHAPOLY_SHA256", f, plain_len,
      QUICTest_benchmark0(test_idx1, plain, plain_len, initial_pn, dcid, dcil,
        scid, scil, token, token_len, f));
  }
  */
  for (uint32_t i = 0; fragment_sizes[i] != 0; ++i) {
    uint32_t f = fragment_sizes[i];
    QUIC_Impl_state_s *st_enc = NULL;

    QUIC_Impl_create_in(test_idx2, &st_enc, initial_pn, test_traffic_secret);
    TIME_AND_TSC("1M encrypt/decrypt AES128_SHA256", f, plain_len,
      QUICTest_benchmark0(st_enc, plain, plain_len, initial_pn, dcid, dcil,
        scid, scil, token, token_len, f));
  }

  /*
  for (uint32_t i = 0; fragment_sizes[i] != 0; ++i) {
    uint32_t f = fragment_sizes[i];
    TIME_AND_TSC("1M encrypt/decrypt AES256_SHA384", f, plain_len,
      QUICTest_benchmark0(test_idx3, plain, plain_len, initial_pn, dcid, dcil,
        scid, scil, token, token_len, f));
  }
  */

}

int main () {
  QUICTest_benchmark();
  if (QUICTest_test(test_idx1, test_plain, test_plain_len)) {
    printf("SUCCESS\n");
    return EXIT_SUCCESS;
  } else {
    printf("FAILURE\n");
    return EXIT_FAILURE;
  }
}
