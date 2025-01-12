
// git-issue2.dfy

ghost function sp_op_const(c: int): int
{
  c
}

ghost predicate {:opaque} InBounds(s: sp_state, o: operand, v: int)
{
  0 <= o < 4294967296
}

lemma lemma_K_InBounds()
  ensures forall s: sp_state :: InBounds(s, sp_op_const(1116352408), 1116352408) && InBounds(s, sp_op_const(1899447441), 1899447441) && InBounds(s, sp_op_const(3049323471), 3049323471) && InBounds(s, sp_op_const(3921009573), 3921009573) && InBounds(s, sp_op_const(961987163), 961987163) && InBounds(s, sp_op_const(1508970993), 1508970993) && InBounds(s, sp_op_const(2453635748), 2453635748) && InBounds(s, sp_op_const(2870763221), 2870763221) && InBounds(s, sp_op_const(3624381080), 3624381080) && InBounds(s, sp_op_const(310598401), 310598401) && InBounds(s, sp_op_const(607225278), 607225278) && InBounds(s, sp_op_const(1426881987), 1426881987) && InBounds(s, sp_op_const(1925078388), 1925078388) && InBounds(s, sp_op_const(2162078206), 2162078206) && InBounds(s, sp_op_const(2614888103), 2614888103) && InBounds(s, sp_op_const(3248222580), 3248222580) && InBounds(s, sp_op_const(3835390401), 3835390401) && InBounds(s, sp_op_const(4022224774), 4022224774) && InBounds(s, sp_op_const(264347078), 264347078) && InBounds(s, sp_op_const(604807628), 604807628) && InBounds(s, sp_op_const(770255983), 770255983) && InBounds(s, sp_op_const(1249150122), 1249150122) && InBounds(s, sp_op_const(1555081692), 1555081692) && InBounds(s, sp_op_const(1996064986), 1996064986) && InBounds(s, sp_op_const(2554220882), 2554220882) && InBounds(s, sp_op_const(2821834349), 2821834349) && InBounds(s, sp_op_const(2952996808), 2952996808) && InBounds(s, sp_op_const(3210313671), 3210313671) && InBounds(s, sp_op_const(3336571891), 3336571891) && InBounds(s, sp_op_const(3584528711), 3584528711) && InBounds(s, sp_op_const(113926993), 113926993) && InBounds(s, sp_op_const(338241895), 338241895) && InBounds(s, sp_op_const(666307205), 666307205) && InBounds(s, sp_op_const(773529912), 773529912) && InBounds(s, sp_op_const(1294757372), 1294757372) && InBounds(s, sp_op_const(1396182291), 1396182291) && InBounds(s, sp_op_const(1695183700), 1695183700) && InBounds(s, sp_op_const(1986661051), 1986661051) && InBounds(s, sp_op_const(2177026350), 2177026350) && InBounds(s, sp_op_const(2456956037), 2456956037) && InBounds(s, sp_op_const(2730485921), 2730485921) && InBounds(s, sp_op_const(2820302411), 2820302411) && InBounds(s, sp_op_const(3259730800), 3259730800) && InBounds(s, sp_op_const(3345764771), 3345764771) && InBounds(s, sp_op_const(3516065817), 3516065817) && InBounds(s, sp_op_const(3600352804), 3600352804) && InBounds(s, sp_op_const(4094571909), 4094571909) && InBounds(s, sp_op_const(275423344), 275423344) && InBounds(s, sp_op_const(430227734), 430227734) && InBounds(s, sp_op_const(506948616), 506948616) && InBounds(s, sp_op_const(659060556), 659060556) && InBounds(s, sp_op_const(883997877), 883997877) && InBounds(s, sp_op_const(958139571), 958139571) && InBounds(s, sp_op_const(1322822218), 1322822218) && InBounds(s, sp_op_const(1537002063), 1537002063) && InBounds(s, sp_op_const(1747873779), 1747873779) && InBounds(s, sp_op_const(1955562222), 1955562222) && InBounds(s, sp_op_const(2024104815), 2024104815) && InBounds(s, sp_op_const(2227730452), 2227730452) && InBounds(s, sp_op_const(2361852424), 2361852424) && InBounds(s, sp_op_const(2428436474), 2428436474) && InBounds(s, sp_op_const(2756734187), 2756734187) && InBounds(s, sp_op_const(3204031479), 3204031479) && InBounds(s, sp_op_const(3329325298), 3329325298)
{
}

type sp_state(!new)

type operand = int
