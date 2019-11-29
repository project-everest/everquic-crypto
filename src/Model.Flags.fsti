module Model.Flags

inline_for_extraction  val model : bool
type ideal_flag = b:bool{b ==> model}

inline_for_extraction val ideal_TS: ideal_flag
inline_for_extraction val ideal_AEAD : f:ideal_flag{b2t f ==> b2t ideal_TS}
inline_for_extraction val ideal_PRF : f:ideal_flag{b2t f ==> b2t ideal_AEAD}
