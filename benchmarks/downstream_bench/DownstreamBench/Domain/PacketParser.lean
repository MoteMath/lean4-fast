import DownstreamBench.BV.SimdLanePack

namespace DownstreamBench.Domain

structure PacketHdr where
  version : BitVec 4
  ihl : BitVec 4
  flags : BitVec 8
  totalLen : BitVec 16
  deriving Repr, DecidableEq

def encodeHdr (h : PacketHdr) : BitVec 32 :=
  (0#28 ++ h.version) |||
  ((0#28 ++ h.ihl) <<< 4#32) |||
  ((0#24 ++ h.flags) <<< 8#32) |||
  ((0#16 ++ h.totalLen) <<< 16#32)

def decodeHdr (w : BitVec 32) : PacketHdr where
  version := w.truncate 4
  ihl := (w >>> 4#32).truncate 4
  flags := (w >>> 8#32).truncate 8
  totalLen := (w >>> 16#32).truncate 16

theorem decode_encode_version (v ihl : BitVec 4) (fl : BitVec 8) (len : BitVec 16) :
    (decodeHdr (encodeHdr ⟨v, ihl, fl, len⟩)).version = v := by
  dsimp [decodeHdr, encodeHdr]
  bv_decide

theorem decode_encode_ihl (v ihl : BitVec 4) (fl : BitVec 8) (len : BitVec 16) :
    (decodeHdr (encodeHdr ⟨v, ihl, fl, len⟩)).ihl = ihl := by
  dsimp [decodeHdr, encodeHdr]
  bv_decide

theorem decode_encode_flags (v ihl : BitVec 4) (fl : BitVec 8) (len : BitVec 16) :
    (decodeHdr (encodeHdr ⟨v, ihl, fl, len⟩)).flags = fl := by
  dsimp [decodeHdr, encodeHdr]
  bv_decide

theorem decode_encode_len (v ihl : BitVec 4) (fl : BitVec 8) (len : BitVec 16) :
    (decodeHdr (encodeHdr ⟨v, ihl, fl, len⟩)).totalLen = len := by
  dsimp [decodeHdr, encodeHdr]
  bv_decide

theorem decode_encode_roundtrip (h : PacketHdr) :
    decodeHdr (encodeHdr h) = h := by
  cases h with
  | mk v ihl fl len =>
    have h1 := decode_encode_version v ihl fl len
    have h2 := decode_encode_ihl v ihl fl len
    have h3 := decode_encode_flags v ihl fl len
    have h4 := decode_encode_len v ihl fl len
    cases h_dec : decodeHdr (encodeHdr ⟨v, ihl, fl, len⟩) with
    | mk dv di df dl =>
      rw [h_dec] at h1 h2 h3 h4
      dsimp only at h1 h2 h3 h4
      subst h1; subst h2; subst h3; subst h4
      rfl

end DownstreamBench.Domain
