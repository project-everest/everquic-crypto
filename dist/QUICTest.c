

#include "QUICTest.h"

#include "internal/LowStar.h"

EverQuic_index
QUICTest_idx =
  { .hash_alg = Spec_Hash_Definitions_SHA2_256, .aead_alg = Spec_Agile_AEAD_CHACHA20_POLY1305 };

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
        LowStar_Printf_print_string("unknown error\n");
        return false;
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

exit_code QUICTest_test(void)
{
  EverQuic_state_s *st_enc = NULL;
  EverQuic_state_s *st_dec = NULL;
  uint8_t
  traffic_secret[32U] =
    {
      0x48U, 0xc4U, 0x30U, 0x9bU, 0x5fU, 0x27U, 0x52U, 0xe8U, 0x12U, 0x7bU, 0x1U, 0x66U, 0x5U, 0x5aU,
      0x9aU, 0x56U, 0xe5U, 0xf9U, 0x6U, 0x31U, 0xe0U, 0x84U, 0x85U, 0xe0U, 0xf8U, 0x9eU, 0x9cU,
      0xecU, 0x4aU, 0xdeU, 0xb6U, 0x50U
    };
  uint64_t initial_pn = 0ULL;
  uint8_t plain[10U] = { 0U, 1U, 2U, 3U, 4U, 5U, 6U, 7U, 8U, 9U };
  uint32_t plain_len = 10U;
  uint8_t dcil8 = 20U;
  uint32_t dcil = (uint32_t)dcil8;
  KRML_CHECK_SIZE(sizeof (uint8_t), dcil);
  uint8_t dcid[dcil];
  memset(dcid, 0U, dcil * sizeof (uint8_t));
  uint32_t scil = 20U;
  KRML_CHECK_SIZE(sizeof (uint8_t), scil);
  uint8_t scid[scil];
  memset(scid, 0U, scil * sizeof (uint8_t));
  uint32_t token_len = 16U;
  KRML_CHECK_SIZE(sizeof (uint8_t), token_len);
  uint8_t token[token_len];
  memset(token, 0U, token_len * sizeof (uint8_t));
  uint32_t cipher_len = plain_len + 16U;
  uint32_t pn_len = 3U;
  uint32_t payload_and_pn_len = cipher_len + pn_len;
  uint32_t version = 0xff000017U;
  EverQuic_long_header_specifics
  hdr_spec =
    {
      .tag = EverQuic_BInitial,
      {
        .case_BInitial = {
          .reserved_bits = 0U, .payload_and_pn_length = (uint64_t)payload_and_pn_len,
          .packet_number_length = pn_len, .token = token, .token_length = token_len
        }
      }
    };
  EverQuic_header
  hdr =
    {
      .tag = EverQuic_BLong,
      {
        .case_BLong = {
          .version = version, .dcid = dcid, .dcil = dcil, .scid = scid, .scil = scil,
          .spec = hdr_spec
        }
      }
    };
  uint32_t public_hdr_len = EverQuic_public_header_len(hdr);
  uint32_t hdr_len = public_hdr_len + pn_len;
  uint32_t enc_dst_len = hdr_len + cipher_len;
  KRML_CHECK_SIZE(sizeof (uint8_t), enc_dst_len);
  uint8_t enc_dst[enc_dst_len];
  memset(enc_dst, 0U, enc_dst_len * sizeof (uint8_t));
  uint64_t enc_dst_pn = initial_pn;
  EverQuic_result
  dec_dst = { .pn = 0ULL, .header = hdr, .header_len = 0U, .plain_len = 0U, .total_len = 0U };
  EverCrypt_Error_error_code
  r = EverQuic_create_in(QUICTest_idx, &st_enc, initial_pn, traffic_secret);
  LowStar_Printf_print_string("Performing ");
  LowStar_Printf_print_string("create_in st_enc");
  LowStar_Printf_print_string(": ");
  if (!QUICTest_is_success_body(r))
    return EXIT_FAILURE;
  else
  {
    EverQuic_state_s *st_enc1 = st_enc;
    EverCrypt_Error_error_code
    r1 = EverQuic_encrypt(st_enc1, enc_dst, &enc_dst_pn, hdr, plain, plain_len);
    LowStar_Printf_print_string("Performing ");
    LowStar_Printf_print_string("encrypt");
    LowStar_Printf_print_string(": ");
    if (!QUICTest_is_success_body(r1))
      return EXIT_FAILURE;
    else
    {
      uint64_t pn = enc_dst_pn;
      EverCrypt_Error_error_code
      r2 = EverQuic_create_in(QUICTest_idx, &st_dec, initial_pn, traffic_secret);
      LowStar_Printf_print_string("Performing ");
      LowStar_Printf_print_string("create_in st_dec");
      LowStar_Printf_print_string(": ");
      if (!QUICTest_is_success_body(r2))
        return EXIT_FAILURE;
      else
      {
        EverQuic_state_s *st_dec1 = st_dec;
        EverCrypt_Error_error_code
        r3 = EverQuic_decrypt(st_dec1, &dec_dst, enc_dst, enc_dst_len, dcil8);
        LowStar_Printf_print_string("Performing ");
        LowStar_Printf_print_string("decrypt");
        LowStar_Printf_print_string(": ");
        if (!QUICTest_is_success_body(r3))
          return EXIT_FAILURE;
        else
        {
          EverQuic_result res = dec_dst;
          LowStar_Printf_print_string("Checking ");
          LowStar_Printf_print_string("pn");
          LowStar_Printf_print_string(": ");
          if (!QUICTest_check_is_true_body(res.pn == pn))
            return EXIT_FAILURE;
          else
          {
            LowStar_Printf_print_string("Checking ");
            LowStar_Printf_print_string("header_len");
            LowStar_Printf_print_string(": ");
            if (!QUICTest_check_is_true_body(res.header_len == hdr_len))
              return EXIT_FAILURE;
            else
            {
              LowStar_Printf_print_string("Checking ");
              LowStar_Printf_print_string("plain_len");
              LowStar_Printf_print_string(": ");
              if (!QUICTest_check_is_true_body(res.plain_len == plain_len))
                return EXIT_FAILURE;
              else
              {
                LowStar_Printf_print_string("Checking ");
                LowStar_Printf_print_string("total_len");
                LowStar_Printf_print_string(": ");
                if (!QUICTest_check_is_true_body(res.total_len == enc_dst_len))
                  return EXIT_FAILURE;
                else
                {
                  uint8_t *plain_ = enc_dst + hdr_len;
                  bool chk = QUICTest_is_equal(plain_, plain, plain_len);
                  LowStar_Printf_print_string("Checking ");
                  LowStar_Printf_print_string("plain");
                  LowStar_Printf_print_string(": ");
                  if (!QUICTest_check_is_true_body(chk))
                    return EXIT_FAILURE;
                  else
                    return EXIT_SUCCESS;
                }
              }
            }
          }
        }
      }
    }
  }
}

