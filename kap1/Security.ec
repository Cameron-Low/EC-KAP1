require import AllCore FSet FMap List Distr DProd PROM KAP1 Games.
require (*  *) StdBigop StdOrder.
(*   *) import AKEc AEADc PRFc StdBigop.Bigreal.BRA StdOrder.RealOrder.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

(* AEAD Reduction *)
module (AEAD_Reduction (D : AKE_Adversary) : AEAD_Adversary) (O : AEAD_Oracles) = {
  module R : AKE_Oracles_i = Game1a with {
    - var psk_map
    proc init_mem [ -1 - ]
    proc gen_pskey [ ^if ~ { O.gen(a, b); } ]
    proc send_msg1 [
      var ex : bool
      ^if + ^ { ex <@ O.ex(a, b); }
      ^if ~ ((a, i) \notin state_map /\ ex)
      ^if.^ca<$ ~ {
        mo <@ O.enc((a, b), msg1_data a b, na);
        ca <- oget mo;
      }
    ]
    proc send_msg2 [
      var ex : bool
      var n : nonce option
      ^if + ^ { ex <@ O.ex(a, b); }
      ^if ~ ((b, j) \notin state_map /\ ex)
      ^if.^match + ^ { n <@ O.dec((a, b), msg1_data a b, ca); }
      ^if.^match ~ (n)
      ^if.^match#Some.^cb<$ ~ {
        mo <@ O.enc((a, b), msg2_data a b ca, nb);
        cb <- oget mo;
      }
    ]
    proc send_msg3 [
      var n : nonce option
      ^if.^match#IPending.^match + ^ { n <@ O.dec((m1.`1, b), msg2_data m1.`1 b m1.`2, m2); }
      ^if.^match#IPending.^match ~ (n)
      ^if.^match#IPending.^match#Some.^cok<$ ~ {
        mo <@ O.enc((m1.`1, b), msg3_data m1.`1 b m1.`2 m2, nok);
        cok <- oget mo;
      }
    ]
    proc send_fin [
      var n : nonce option
      ^if.^match#RPending.^match + ^ { n <@ O.dec((m1.`1, b), msg3_data m1.`1 b m1.`2 m2, m3); }
      ^if.^match#RPending.^match ~ (n)
    ]
  }

  proc run(b) = {
    var b';
    R.init_mem(b);
    b' <@ D(R).run();
    return b';
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* ROM Reduction *)

clone PROM.FullRO as NROc with
  type in_t    <= msg_data * ctxt,
  type out_t   <= nonce,
  op   dout  _ <= dnonce,
  type d_in_t  <= bool,
  type d_out_t <= bool
proof *.

module (Nonce_Delay_Reduction (D : AKE_Adversary) : NROc.RO_Distinguisher) (O : NROc.RO) = {
  module R : AKE_Oracles_i = Game3b with {
    - var nonce_map
    proc init_mem [ -1 - ]
    proc send_msg1 [
      ^if.^if.:[^na<$ .. 2] ~ { O.sample((msg1_data a b, ca)); }
    ]
    proc send_msg2 [
      ^if.^match#Some.^if.:[^nb<$ .. ^ <-] ~ { O.sample((msg2_data a b ca, cb)); }
    ]
    proc send_msg3 [
      var nb' : nonce
      ^if.^match#IPending.^match#Some.^if.^k<- ~ {
        na <@ O.get((msg1_data m1.`1 b, m1.`2));
        nb' <@ O.get((msg2_data m1.`1 b m1.`2, m2));
        k <- prf (na, nb') (m1.`1, b);
      }
    ]
    proc send_fin [
      ^if.^match#RPending.^match#Some.^k<- ~ {
        na <@ O.get((msg1_data m1.`1 b, m1.`2));
        nb <@ O.get((msg2_data m1.`1 b m1.`2, m2));
        k <- prf (na, nb) (m1.`1, b);
      }
    ]
  }

  proc distinguish(b) = {
    var b';
    R.init_mem(b);
    b' <@ D(R).run();
    return b';
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* PRF Reduction *)

module (PRF_Reduction (D : AKE_Adversary) : PRF_Adversary) (O : PRF_Oracles) = {
  module R : AKE_Oracles_i = Game4 with {
    - var prfkey_map
    proc init_mem [ ^b0<- & +1 -]
    proc send_msg3 [
      var ko : skey option
      ^if.^match#IPending.^match#Some.^if.:[^na<$ .. ^k<-] ~ {
        O.gen((msg3_data m1.`1 b m1.`2 m2, cok));
        ko <@ O.f((msg3_data m1.`1 b m1.`2 m2, cok), (m1.`1, b));
        k <- oget ko;
      }
    ]
    proc send_fin [
      var ko : skey option
      ^if.^match#RPending.^match#Some.^k<- ~ {
        ko <@ O.f((msg3_data m1.`1 b m1.`2 m2, m3), (m1.`1, b));
        k <- oget ko;
      }
    ]
  }

  proc run(b) = {
    var b';
    R.init_mem(b);
    b' <@ D(R).run();
    return b';
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* Query Counting *)

op q_m1 : { int | 0 <= q_m1 } as ge0_q_m1.
op q_m2 : { int | 0 <= q_m2 } as ge0_q_m2.
op q_m3 : { int | 0 <= q_m3 } as ge0_q_m3.

module Counter (O : AKE_Oracles_i) : AKE_Oracles_i = {
  var cm1, cm2, cm3 : int

  include O[send_fin, gen_pskey, test, reveal]

  proc init_mem(b: bool) = {
    (cm1, cm2, cm3) <- (0, 0, 0);
    O.init_mem(b);
  }

  proc send_msg1(x) = {
    var m;
    cm1 <- cm1 + 1;
    m <@ O.send_msg1(x);
    return m;
  }
  proc send_msg2(x) = {
    var m;
    cm2 <- cm2 + 1;
    m <@ O.send_msg2(x);
    return m;
  }
  proc send_msg3(x) = {
    var m;
    cm3 <- cm3 + 1;
    m <@ O.send_msg3(x);
    return m;
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* ROM Reduction skeys *)

clone PROM.FullRO as KROc with
  type in_t    <= trace,
  type out_t   <= skey,
  op   dout  _ <= dskey,
  type d_in_t  <= bool,
  type d_out_t <= bool
proof *.

module (Key_Delay_Reduction (D : AKE_Adversary) : KROc.RO_Distinguisher) (O : KROc.RO) = {
  module R : AKE_Oracles_i = Game5a with {
    proc init_mem [ -1 - ]
    proc send_msg3 [ ^if.^match#IPending.^match#Some.^if.^k<- + ^ { O.sample((m1, m2, cok)); } ]
    proc reveal [
      var k' : skey
      ^if.^match#Accepted.^if.1 ~ {
        k' <@ O.get(t);
        ko <- Some k';
      }
    ]
    proc test [
      ^if.^match#Accepted.^if.1 ~ {
        k' <@ O.get(t);
        if (b0 = false) {
          k' <- k';
        } else {
          k' <$ dskey;
        }
      }
    ]
  }

  proc distinguish(b) = {
    var b';
    R.init_mem(b);
    b' <@ D(R).run();
    return b';
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: AKE_Adversary {
  -AKE_Oracles, -Counter,
  -AEAD_Oracles_0, -AEAD_Oracles_1,
  -PRF_Oracles_0, -PRF_Oracles_1,
  -AEAD_Reduction, -PRF_Reduction,
  -Nonce_Delay_Reduction, -NROc.RO, -NROc.FRO,
  -Key_Delay_Reduction, -KROc.RO, -KROc.FRO,
  -Game1, -Game1a,
  -Game2,
  -Game3, -Game3a, -Game3b, -Game3c, -Game3d,
  -Game4,
  -Game5, -Game5a, -Game5b, -Game5c
}.

declare axiom A_ll:
  forall (O <: AKE_Oracles { -A }),
  islossless O.gen_pskey =>
  islossless O.send_msg1 =>
  islossless O.send_msg2 =>
  islossless O.send_msg3 =>
  islossless O.send_fin =>
  islossless O.reveal =>
  islossless O.test =>
  islossless A(O).run.

declare axiom A_bounded_qs:
  forall (O <: AKE_Oracles_i { -A }),
  hoare[A(Counter(O)).run:
        Counter.cm1 = 0 /\ Counter.cm2 = 0 /\ Counter.cm3 = 0
    ==> Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2 /\ Counter.cm3 <= q_m3
  ].

(* ------------------------------------------------------------------------------------------ *)
(* Hop 1: AKE Game to Game 1 - Inline procedure calls *) 
  
lemma Hop1 bit &m:
    Pr[AKE_Game(AKE_Oracles(KAP1), A).run(bit) @ &m : res] = Pr[AKE_Game(Game1, A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={b0, state_map, psk_map}(AKE_Oracles, Game1) ).
+ by sim.
+ proc; inline.
  sp; if => //.
  by auto.
+ proc; inline.
  sp; if => //.
  sp; match = => //.
  + match None {1} ^match; 1: by auto.
    by auto.
  move => na.
  match Some {1} ^match; 1: by auto => /#.
  by auto.
+ proc; inline.
  sp; if => //.
  sp; match =; try by auto.
  + smt().
  move => si m1.
  sp; match = => //.
  + match None {1} ^match; 1: by auto.
    by auto.
  move => nb.
  match Some {1} ^match; 1: by auto => /#.
  by auto.
+ proc; inline.
  sp; if => //.
  sp; match =; try by auto.
  + smt().
  move => sr m1 m2.
  sp; match = => //.
  + match None {1} ^match; 1: by auto.
    by auto.
  move => nok.
  match Some {1} ^match; 1: by auto => /#.
  by auto.
+ by sim.
+ by sim.
by auto.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 2: Game 1 to Game 1a - cleanup session state redundancies *) 

local op clean1 (s : session_state) =
match s with
| IPending st m1 =>
  let (id, psk, na, ca) = st in IPending (id, witness, na, witness) m1
| RPending st m1 m2 =>
  let (id, psk, na, nb, ca, cb) = st in RPending (witness, witness, na, nb, witness, witness) m1 m2
| Accepted _ _ => s
| Observed _ _ => s
| Aborted   => s
end.

local lemma clean1_trace s: trace (clean1 s) = trace s.
proof.
by case s=> //; move=> [] //=.
qed.

local lemma clean1_fresh h sml smr:
  (forall h, omap (fun (v: _ * _) => let (r, s) = v in (r, clean1 s)) sml.[h] = smr.[h]) =>
  fresh h sml <=> fresh h smr.
proof.
move=> eq_sm.
rewrite /fresh /observed_partners.
suff -> : partners h sml = partners h smr.
+ do! congr.
  rewrite fun_ext => h'.
  rewrite -(eq_sm h') //=.
  case: (sml.[h'])=> //.
  by move => [r' []] // [].
rewrite fsetP=> h'.
rewrite !mem_fdom !mem_filter /=.
rewrite !fmapP.
rewrite -(eq_sm h') -!(eq_sm h) /=.
case: (sml.[h'])=> //=.
move=> [r s].
have -> : exists y, (r, s) = y by exists (r, s).
have -> : exists y, (r, clean1 s) = y by exists (r, clean1 s).
case: (sml.[h])=> /=.
+ by rewrite clean1_trace.
move=> [r' s'] /=.
rewrite !clean1_trace.
by case s'.
qed.

lemma Hop2 bit &m:
    Pr[AKE_Game(Game1, A).run(bit) @ &m : res] = Pr[AKE_Game(Game1a, A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline*.
call (:
    ={b0, psk_map}(Game1, Game1a)
/\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
/\ (forall a i, Game1_inv Game1.state_map Game1.psk_map a i){1}
).
- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_gen_pskey _ => //.
  proc.
  by if; auto.

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_send_msg1 _ => //.
  proc; inline.
  sp; wp; if => //.
  + smt().
  auto => />.
  smt(get_setE).

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_send_msg2 _ => //.
  proc; inline.
  sp; wp; if => //.
  + smt().
  sp; match =.
  + smt().
  + auto => />.
    smt(get_setE).
  by auto; smt(get_setE).

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_send_msg3 _ => //.
  proc; inline.
  sp; wp; if => //.
  + smt().
  sp; match; 1..5: (
    move => &1 &2 /> + + /(_ (a, i){2});
    rewrite domE;
    case: (Game1.state_map{1}.[a, i]{2})=> />;
    move => + H;
    by rewrite -H => /#
  ); ~1: by auto.
  move => sil m1l sir m1r.
  sp; match =.
  + auto => />.
    smt(get_setE).
  + by auto; smt(get_setE).
  auto => />.
  smt(get_setE).

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_send_fin _ => //.
  proc; inline.
  sp; if => //.
  + smt().
  sp; match; 1..5: (
    move => &1 &2 /> + + /(_ (b, j){2});
    rewrite domE;
    case: (Game1.state_map{1}.[b, j]{2}) => />;
    move => + H;
    by rewrite -H /#
  ); ~2: by auto.
  move => sil m1l m2l sir m1r m2r.
  sp; match =.
  + auto => />.
    smt().
  + auto => />.
    smt(get_setE).
  auto => />.
  smt(get_setE).

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
  ) Game1_inv_reveal _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match; 1..5:(
    move => &1 &2 /> + + /(_ h{2});
    rewrite domE;
    case: (Game1.state_map{1}.[h]{2}) => />;
    move => + H;
    by rewrite -H => /#
  ); ~3: by auto.
  move => tr k tr' k'.
  if => //.
  + move => &1 &2 |> *.
    by rewrite (clean1_fresh h{2} Game1.state_map{1} Game1a.state_map{2}).
  auto => /> &1 &2 + + eq_sm invl a_in _.
  rewrite -(eq_sm h{2}).
  move => *.
  split; 1: smt().
  move => h'.
  case (h' = h{2}) => [|hneq].
  + smt(get_set_sameE).
  rewrite !get_set_neqE //.
  by rewrite eq_sm.

- conseq (: ={res}
          /\ ={b0, psk_map}(Game1, Game1a)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clean1 s)) Game1.state_map.[h]{1} = Game1a.state_map.[h]{2})
     ) Game1_inv_test _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match; 1..5:(
    move => &1 &2 /> + + /(_ h{2});
    rewrite domE;
    case: (Game1.state_map{1}.[h]{2}) => />;
    move => + H;
    by rewrite -H => /#
  ); ~3: by auto.
  move => tr k tr' k'.
  if => //.
  + move => &1 &2 |> *.
    by rewrite (clean1_fresh h{2} Game1.state_map{1} Game1a.state_map{2}).
  if => //.
  - auto => /> &1 &2 + + eq_sm invl a_in _.
    rewrite -(eq_sm h{2}).
    move => *.
    split; 1: smt().
    move => h'.
    case (h' = h{2}) => [|hneq].
    + smt(get_set_sameE).
    rewrite !get_set_neqE //.
    by rewrite eq_sm.
  auto => /> &1 &2 + + eq_sm invl a_in _.
  rewrite -(eq_sm h{2}).
  move => 7? h'.
  case (h' = h{2}) => [|hneq].
  + smt(get_set_sameE).
  rewrite !get_set_neqE //.
  by rewrite eq_sm.

auto=> />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1a to Game 2 - Apply the AEAD assumption. *)

lemma Hop3 bit &m:
    `|Pr[AKE_Game(Game1a, A).run(bit) @ &m : res] - Pr[AKE_Game(Game2, A).run(bit) @ &m : res]|
  =
    `|Pr[AEAD_Game(AEAD_Oracles_0, AEAD_Reduction(A)).run(bit) @ &m : res] - Pr[AEAD_Game(AEAD_Oracles_1, AEAD_Reduction(A)).run(bit) @ &m : res]|.
proof.
do! congr.
+ byequiv => //.
  proc; inline*.
  wp.
  call (:
        ={b0, state_map}(Game1a, AEAD_Reduction.R)
     /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
     /\ (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i){1}
  ) => //.

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_gen_pskey _ => //.
    by proc; inline; sp; if; auto.

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_send_msg1 _ => //.
    proc; inline.
    sp; wp; if => //.
    by match Some {2} ^match; auto; smt().

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_send_msg2 _ => //.
    proc; inline.
    sp; wp; if => //.
    match Some {2} ^match.
    + auto; smt().
    sp; match =.
    + by move => /> /#.
    + by auto.
    move => na.
    by match Some {2} ^match; auto; smt().

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_send_msg3 _ => //.
    proc; inline.
    sp; wp; if=> //.
    sp; match = => //.
    + smt().
    move=> st m1.
    exlim Game1a.state_map{1}, Game1a.psk_map{1}, a{1}, i{1} => sm pm a i.
    case @[ambient] _: (forall a i, Game1a_inv sm pm a i) => [inv|?]; 2: by exfalso => /#.
    match Some {2} ^match.
    + auto => />.
      smt(get_setE).
    sp; match =.
    + by auto => /> /#.
    + by auto => /> /#.
    move => nb.
    match Some {2} ^match.
    + auto => />.
      smt(get_setE).
    by auto => /> /#.

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_send_fin _ => //.
    proc; inline.
    sp; if=> //.
    sp; match = => //.
    + move=> /#.
    move=> st m1 m2.
    match Some {2} ^match.
    + auto=> />.
      smt(get_setE).
    by sp; match =; auto=> /> /#.

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_reveal _ => //.
    by sim.

  - conseq (: ={res}
         /\ ={b0, state_map}(Game1a, AEAD_Reduction.R)
         /\ Game1a.psk_map{1} = AEAD_Oracles_common.key_map{2}
    ) Game1a_inv_test _ => //.
    by sim.

  auto => />.
  smt(emptyE).

byequiv => //.
proc; inline*.
wp.
call (:
         ={b0, state_map}(Game2, AEAD_Reduction.R)
      /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
      /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
      /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
      /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
      /\ (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i){1}
).
- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_gen_pskey _ => //.
  proc; inline; sp.
  by if; auto.

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_send_msg1 _ => //.
  proc; inline.
  sp; wp; if => //.
  rcondt{2} ^if; 1: by auto.
  swap {2} ^c<$ @ ^na<$.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_send_msg2 _ => //.
  proc; inline.
  sp; wp; if => //.
  rcondt {2} 5; 1: by auto.
  sp; match =.
  + smt().
  + by auto.
  move=> na.
  rcondt {2} ^if; 1: by auto.
  swap {2} ^c0<$ @ ^nb<$.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_send_msg3 _ => //.
  proc; inline.
  sp; wp; if => //.
  sp; match = => //.
  + smt().
  move=> st m1.
  rcondt {2} ^if.
  + auto => />.
    smt(get_setE).
  sp; match =.
  + smt().
  + by auto.
  move => nb.
  rcondt {2} ^if.
  + auto => />.
    smt(get_setE).
  swap {2} ^c0<$ @ ^nok<$.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_send_fin _ => //.
  proc; inline.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => st m1 m2.
  rcondt {2} 6.
  + auto=> />.
    smt(get_setE).
  by sp; match =; auto; smt(get_setE).

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_reveal _ => //.
  by sim />.

- conseq (: ={res}
         /\ ={b0, state_map}(Game2, AEAD_Reduction.R)
         /\ Game2.psk_map{1} = AEAD_Oracles_common.key_map{2}
         /\ (forall a b m1, Game2.dec_map{1}.[msg1_data a b, m1] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg1_data a b, m1])
         /\ (forall a b m1 m2, Game2.dec_map{1}.[msg2_data a b m1, m2] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg2_data a b m1, m2])
         /\ (forall a b m1 m2 m3, Game2.dec_map{1}.[msg3_data a b m1 m2, m3] = AEAD_Oracles_1.dec_map{2}.[(a, b), msg3_data a b m1 m2, m3])
  ) Game2_inv_test _ => //.
  by sim />.
 
auto => />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 4: Game 2 to Game 3 - Remove collisions of all produced ciphertexts. *)

lemma Hop4 bit &m: `| Pr[AKE_Game(Game2, A).run(bit) @ &m : res] - Pr[AKE_Game(Game3, A).run(bit) @ &m : res] | <= Pr[AKE_Game(Game2, A).run(bit) @ &m : Game2.bad].
proof.
rewrite distrC.
byequiv (: _ ==> _) : Game3.bad => //; first last.
+ move => &1 &2.
  by case: (Game2.bad{2}).
symmetry; proc; inline*.
call (: Game3.bad, ={b0, bad, psk_map, state_map, dec_map}(Game2, Game3), ={bad}(Game2, Game3)) => //.
+ exact A_ll.

+ by proc; inline*; auto; if; auto.
+ move => &2 ->.
  proc; sp; if; auto => />.
  by rewrite dpskey_ll.
+ move => &1.
  proc; sp; if; auto.
  by rewrite dpskey_ll.

+ proc.
  sp; wp; if => //.
  seq 1 1: (#pre /\ ={ca}); 1: by auto.
  sp 1 1.
  by if{2}; auto => />.
+ move => &2 ->.
  proc; sp; if => //; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move => &1.
  proc; sp; wp; if => //.
  rcondf ^if; auto => />.
  by rewrite dctxt_ll.

+ proc.
  sp; wp; if => //.
  match = => //.
  + by auto.
  move => na.
  seq 1 1: (#pre /\ ={cb}); 1: by auto.
  sp 0 1.
  by if{2}; auto => />.
+ move => &2 ->.
  proc; sp; wp; if => //; match =; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move => &1.
  proc; sp; wp; if => //; match =; auto.
  rcondf ^if; auto => />.
  by rewrite dctxt_ll.

+ proc.
  sp; wp; if => //.
  sp; match = => //.
  - smt().
  move => s m1.
  sp; match = => //.
  + by auto.
  move => nb.
  seq 1 1: (#pre /\ ={cok}); 1: by auto.
  sp 0 1.
  by if{2}; auto=> />.
+ move => &2 ->.
  proc; sp; wp; if => //; sp; match =; auto; sp; match =; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move => &1.
  proc; sp; wp; if => //; sp; match =; auto; sp; match =; auto.
  rcondf ^if; auto => />.
  by rewrite dctxt_ll.

+ proc.
  sp; if=> //.
  sp; match =; auto; smt().
+ move => &2 ->.
  proc; sp; if => //; sp; match =; auto; smt().
+ move => &1.
  proc; sp; if => //; sp; match =; auto; smt().

+ proc.
  sp; if => //.
  sp; match =; auto; smt().
+ move => &2 ->.
  proc; sp; if => //; sp; match =; auto; smt().
+ move => &1.
  proc; sp; if => //; sp; match =; auto; smt().

+ proc.
  sp; if => //.
  sp; match =; auto.
  + smt().
  sp; if => //; if => //; auto => /#.
+ move=> &2 ->.
  proc; sp; if => //; sp; match =; auto.
  sp; if => //; if => //.
  + auto => /#.
  auto => />.
  by rewrite dskey_ll.
+ move => &1.
  proc; sp; if => //; sp; match =; auto.
  sp; if => //; if => //.
  + auto => /#.
  auto => />.
  by rewrite dskey_ll.
auto => />.
move => rl rr al bl dl pl sl ar br dr pr sr.
by case : (!br) => />.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 2b: Bound the bad event. *)

lemma Hop4_bound bit &m: Pr[AKE_Game(Game2, A).run(bit) @ &m : Game2.bad] <= 1%r / 2%r * ((q_m1 + q_m2 + q_m3) * (q_m1 + q_m2 + q_m3 - 1))%r * p_max dctxt.
proof.
have ->: Pr[AKE_Game(Game2, A).run(bit) @ &m : Game2.bad]
       = Pr[AKE_Game(Counter(Game2), A).run(bit) @ &m : Game2.bad /\ Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2 /\ Counter.cm3 <= q_m3].
+ byequiv=> //.
  proc; inline; sp.
  conseq (: ==> ={Game2.bad}) _ (: Counter.cm1 = 0 /\ Counter.cm2 = 0 /\ Counter.cm3 = 0 ==> Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2 /\ Counter.cm3 <= q_m3)=> //.
  + by call (A_bounded_qs Game2).
  by call (: ={glob Game2}); ~-1: by proc; inline; sim; auto.
fel
  1
  (Counter.cm1 + Counter.cm2 + Counter.cm3)
  (fun x => x%r * p_max dctxt)
  (q_m1 + q_m2 + q_m3)
  Game2.bad
  [
   Counter(Game2).send_msg1 : ((arg.`1, arg.`2) \notin Game2.state_map /\ (arg.`1, arg.`3) \in Game2.psk_map);
   Counter(Game2).send_msg2 : ((arg.`1, arg.`2) \notin Game2.state_map
                                 /\ (arg.`3.`1, arg.`1) \in Game2.psk_map
                                 /\ (exists na, Game2.dec_map.[msg1_data arg.`3.`1 arg.`1, arg.`3.`2] = Some na));
 Counter(Game2).send_msg3 : ((arg.`1, arg.`2) \in Game2.state_map
                                 /\ (exists r s, (r, s) = oget Game2.state_map.[arg.`1, arg.`2]
                                     /\ exists si m1, s = IPending si m1
                                     /\ exists nb, Game2.dec_map.[msg2_data m1.`1 si.`1 m1.`2, arg.`3] = Some nb))
  ]
  (fsize Game2.dec_map <= Counter.cm1 + Counter.cm2 + Counter.cm3)
  => //.
+ rewrite -mulr_suml StdBigop.Bigreal.sumidE.
  + smt(ge0_q_m1 ge0_q_m2 ge0_q_m3).
  smt().
+ smt().
+ inline; auto=> />.
  by rewrite fsize_empty.

+ proc; inline.
  rcondt ^if; 1: by auto.
  swap ^na<$ @ ^ca<$; wp.
  rnd (fun c => exists u, u \in Game2.dec_map /\ c = snd u).
  move=> bd; auto=> &hr /> *.
  split; last first.
  + move=> _ v _ ad mem.
    by exists (ad, v).
  apply (ler_trans ((fsize Game2.dec_map{hr})%r * p_max dctxt)).
  + apply Mu_mem.mu_mem_le_fsize.
    move=> u _ /=.
    exact pmax_upper_bound.
  smt(pmax_ge0).
+ move=> c.
  proc; inline.
  rcondt ^if; 1: by auto.
  auto=> />.
  smt(fsize_set).
+ move=> b c.
  proc; inline.
  rcondf ^if; 1: by auto.
  by auto=> /#.

+ proc; inline.
  rcondt ^if; 1: by auto.
  match Some ^match; 1: by auto.
  swap ^nb<$ @ ^cb<$; wp.
  rnd (fun c => exists u, u \in Game2.dec_map /\ c = snd u).
  move=> bd; auto=> &hr /> *.
  split; last first.
  + move=> _ v _ ad mem.
    by exists (ad, v).
  apply (ler_trans ((fsize Game2.dec_map{hr})%r * p_max dctxt)).
  + apply Mu_mem.mu_mem_le_fsize.
    move=> u _ /=.
    exact pmax_upper_bound.
  smt(pmax_ge0).
+ move=> c.
  proc; inline.
  rcondt ^if; 1: by auto.
  match Some ^match; 1: by auto=> />.
  auto=> />.
  smt(fsize_set).
+ move=> b c.
  proc; inline.
  sp.
  if; last by auto=> /#.
  by match None ^match; auto=> /#.

+ proc; inline.
  rcondt ^if; 1: by auto.
  match IPending ^match; 1: by auto=> /#.
  match Some ^match; 1: by auto=> /#.
  swap ^nok<$ @ ^cok<$; wp.
  rnd (fun c => exists u, u \in Game2.dec_map /\ c = snd u).
  move=> bd; auto=> &hr /> *.
  split; last first.
  + move=> _ v _ ad mem.
    by exists (ad, v).
  apply (ler_trans ((fsize Game2.dec_map{hr})%r * p_max dctxt)).
  + apply Mu_mem.mu_mem_le_fsize.
    move=> u _ /=.
    exact pmax_upper_bound.
  smt(pmax_ge0).
+ move=> c.
  proc; inline.
  rcondt ^if; 1: by auto.
  match IPending ^match; 1: by auto=> /#.
  match Some ^match; 1: by auto=> /#.
  auto=> />.
  smt(fsize_set).
move=> b c.
proc; inline.
sp.
if; last by auto=> /#.
sp; match; ~1: by auto=> /#.
by sp; match; auto=> /#.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 5: Game 3 to Game 3a - Retrieve nonces from the dec_map not session state. *)

local op clean2 (s : session_state) =
match s with
| IPending st m1 =>
  let (id, psk, na, ca) = st in IPending (id, witness, witness, witness) m1
| RPending st m1 m2 =>
  let (id, psk, na, nb, ca, cb) = st in RPending (witness, witness, witness, witness, witness, witness) m1 m2
| Accepted _ _ => s
| Observed _ _ => s
| Aborted   => s
end.

local lemma clean2_trace s: trace (clean2 s) = trace s.
proof.
by case s=> //; move=> [] //=.
qed.

local lemma clean2_fresh h sml smr:
  (forall h, omap (fun (v: _ * _) => let (r, s) = v in (r, clean2 s)) sml.[h] = smr.[h]) =>
  fresh h sml <=> fresh h smr.
proof.
move=> eq_sm.
rewrite /fresh /observed_partners.
suff -> : partners h sml = partners h smr.
+ do! congr.
  rewrite fun_ext => h'.
  rewrite -(eq_sm h') //=.
  case: (sml.[h'])=> //.
  by move => [r' []] // [].
rewrite fsetP=> h'.
rewrite !mem_fdom !mem_filter /=.
rewrite !fmapP.
rewrite -(eq_sm h') -!(eq_sm h) /=.
case: (sml.[h'])=> //=.
move=> [r s].
have -> : exists y, (r, s) = y by exists (r, s).
have -> : exists y, (r, clean2 s) = y by exists (r, clean2 s).
case: (sml.[h])=> /=.
+ by rewrite clean2_trace.
move=> [r' s'] /=.
rewrite !clean2_trace.
by case s'.
qed.

lemma Hop5 bit &m: Pr[AKE_Game(Game3, A).run(bit) @ &m : res] = Pr[AKE_Game(Game3a, A).run(bit) @ &m :res].
proof.
byequiv (: ={glob A, arg} ==> _) => //.
proc; inline*.
call(: ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
    /\ (forall a i, Game3_inv Game3.state_map Game3.dec_map a i){1}
).

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_gen_pskey _ => //.
  proc.
  by if; auto.

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_send_msg1 _ => //.
  proc; inline*.
  sp; wp; if => //.
  + smt().
  seq 1 1 : (#pre /\ ={ca}); 1: by auto.
  sp; if => //.
  sp; seq 1 1 : (#pre /\ ={na}); 1: by auto=> />.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_send_msg2 _ => //.
  proc; inline*.
  sp; wp; if => //.
  + smt().
  match = => //.
  + by auto; smt(get_setE).
  move => na.
  seq 1 1 : (#pre /\ ={cb}); 1: by auto.
  sp; if => //.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_send_msg3 _ => //.
  proc; inline*.
  sp; wp; if => //.
  + smt().
  sp; match; 1..5: (
    move=> &1 &2 /> + + /(_ (a, i){2});
    rewrite domE;
    case: (Game3.state_map{1}.[(a, i)]{2})=> />;
    move=> + H;
    by rewrite -H => /#
  ); ~1: by auto.
  move => sl m1l sr m1r.
  sp; match = => //.
  + auto => /> /#.
  + by auto => />; smt(get_setE).
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  auto => /> *.
  by do split; smt(get_setE).

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_send_fin _ => //.
  proc; inline*.
  sp; if => //.
  + smt().
  sp; match; 1..5: (
    move=> &1 &2 /> + + /(_ (b, j){2});
    rewrite domE;
    case: (Game3.state_map{1}.[(b, j)]{2})=> />;
    move=> + H;
    by rewrite -H => /#
  ); 1,3..5: by auto.
  move => sl m1l m2l sr m1r m2r.
  sp; match = => //.
  + move => /> /#.
  + by auto => />; smt(get_setE).
  move => nok.
  auto => />.
  smt(get_setE).

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_reveal _ => //.
  proc; inline.
  sp; if => //.
  + smt().
  sp; match; 1..5:(
    move => &1 &2 /> + + /(_ h{2});
    rewrite domE;
    case: (Game3.state_map{1}.[h{2}]) => />;
    move => + H;
    by rewrite -H => /#
  ); ~3: by auto.
  move=> t k t' k'.
  if => //.
  + move => &1 &2 [] |> *.
    by rewrite (clean2_fresh h{2} Game3.state_map{1} Game3a.state_map{2}).
  auto => /> &1 &2 + + eqsm invl a_in _.
  rewrite -(eqsm h{2}).
  move => *.
  split. smt().
  move => h'.
  case (h' = h{2}) => [|hneq].
  smt(get_set_sameE).
  do rewrite get_set_neqE => //.
  by rewrite eqsm.

- conseq (: ={res}
    /\ ={b0, psk_map, bad, dec_map}(Game3, Game3a)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clean2 s)) Game3.state_map.[h]{1} = Game3a.state_map.[h]{2})
  ) Game3_inv_test _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match; 1..5:(
    move => &1 &2 /> + + /(_ h{2});
    rewrite domE;
    case: (Game3.state_map{1}.[h]{2}) => />;
    move => + H;
    by rewrite -H => /#
  ); ~3: by auto.
  move=> t k t' k'.
  if => //.
  + move => &1 &2 [] |> *.
    by rewrite (clean2_fresh h{2} Game3.state_map{1} Game3a.state_map{2}).
  if => //.
  + auto=> /> &1 &2 + + eqsm invl a_in _.
    rewrite -(eqsm h{2}).
    move => *.
    split. smt().
    move => h'.
    case (h' = h{2}) => [|hneq].
    smt(get_set_sameE).
    do rewrite get_set_neqE => //.
    by rewrite eqsm.
  auto=> |> &1 &2 + + eqsm invli invlr _ ideal sk _.
  move => ? ? h'.
  rewrite !get_setE.
  rewrite -!(eqsm h').
  by case (h' = h{2}) => //#.

auto=> />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 6: Game 3a to Game 3b - Store nonces separately to logging decryptions *)
lemma Hop6 bit &m: Pr[AKE_Game(Game3a, A).run(bit) @ &m : res] = Pr[AKE_Game(Game3b, A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={b0, state_map, psk_map, bad}(Game3a, Game3b)
      /\ (forall a b m1, Game3a.dec_map.[msg1_data a b, m1]{1} = Game3b.nonce_map.[msg1_data a b, m1]{2})
      /\ (forall a b m1 m2, Game3a.dec_map.[msg2_data a b m1, m2]{1} = Game3b.nonce_map.[msg2_data a b m1, m2]{2})
      /\ (forall h, h \in Game3a.dec_map{1} <=> h \in Game3b.dec_map{2})
); try by sim />.

+ proc; inline.
  sp; if => //.
  seq 1 1 : (#pre /\ ={ca}); 1: by auto.
  sp; if.
  + smt().
  + sp; seq 1 1 : (#pre /\ ={na}); 1: by auto=> />.
    auto => />.
    smt(get_setE mem_set).
  by auto => /#.

+ proc; inline.
  sp; if => //.
  match; 1,2: smt().
  + by auto; smt().
  move => *.
  seq 1 1 : (#pre /\ ={cb}); 1: by auto.
  sp; if.
  + smt().
  + sp; seq 1 1 : (#pre /\ ={nb}); 1: by auto=> />.
    auto => />.
    smt(get_setE mem_set).
  by auto => /#.

+ proc; inline.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => si m1.
  sp; match; 1,2: smt().
  + by auto; smt().
  move => *.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if.
  + smt().
  + sp; seq 1 1 : (#pre /\ ={nok}); 1: by auto=> />.
    auto => />.
    smt(get_setE).
  by auto => /#.

+ proc; inline.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => sr m1 m2.
  sp; match; 1,2: smt().
  + by auto; smt().
  move => *.
  auto => />.
  smt(get_setE).

by auto.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 7: Game 3b to Game 3c - Delay the sampling of na and nb until first retrieval *)

lemma Hop7 bit &m: Pr[AKE_Game(Game3b, A).run(bit) @ &m : res] = Pr[AKE_Game(Game3c, A).run(bit) @ &m : res].
byequiv => //.
proc*.
transitivity* {1} { r <@ NROc.MainD(Nonce_Delay_Reduction(A), NROc.RO).distinguish(b); }.

+ inline*.
  wp.
  call (: ={b0, state_map, psk_map, dec_map, bad}(Game3b, Nonce_Delay_Reduction.R)
       /\ (Game3b.nonce_map{1} = NROc.RO.m{2})
       /\ (forall a b ca, (msg1_data a b, ca) \in Game3b.dec_map <=> (msg1_data a b, ca) \in Game3b.nonce_map){1}
       /\ (forall a b ca cb, (msg2_data a b ca, cb) \in Game3b.dec_map <=> (msg2_data a b ca, cb) \in Game3b.nonce_map){1}
       /\ (forall a b ca cb, (msg2_data a b ca, cb) \in Game3b.dec_map => (msg1_data a b, ca) \in Game3b.dec_map){1}
       /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game3b.dec_map => (msg2_data a b ca, cb) \in Game3b.dec_map){1}
  ) => //.

  - by proc; sp; if; auto.

  - proc; inline*.
    sp; wp; if => //.
    seq 1 1 : (#pre /\ ={ca}); 1: by auto.
    sp; if => //.
    rcondt {2} ^if; 1: by auto => /#.
    auto => />.
    smt(get_setE).

  - proc; inline*.
    sp; wp; if => //.
    match; 1,2: smt().
    + by auto => />.
    move=> nal nar.
    seq 1 1 : (#pre /\ ={cb}); 1: by auto.
    sp; if => //.
    rcondt {2} ^if; 1: by auto => /#.
    auto => />.
    smt(get_setE).

  - proc; inline*.
    sp; wp; if => //.
    sp; match = => //.
    + smt().
    move => s m1.
    sp; match; 1: smt().
    + move => /> *; smt().
    + by auto => />.
    move => nbl nbr.
    seq 1 1 : (#pre /\ ={cok}); 1: by auto.
    sp; if => //.
    rcondf {2} ^if.
    + auto => />.
      smt(mem_set).
    rcondf {2} ^if.
    + auto => />.
      smt(mem_set).
    auto => />.
    smt(get_setE).

  - proc; inline*.
    sp; if => //.
    sp; match = => //.
    + smt().
    move => s m1 m2.
    sp; match; 1,2: smt().
    + by auto => />.
    move => nokl nokr.
    rcondf {2} ^if; 1: by auto => /#.
    rcondf {2} ^if; 1: by auto => /#.
    auto => />.

  - by sim />.

  - by sim />.

  auto => />.
  smt(emptyE).

rewrite equiv [{1} 1 (NROc.FullEager.RO_LRO (Nonce_Delay_Reduction(A)) _)]; 1: by move=> _; exact dnonce_ll.
inline.
wp; call (:
  ={b0, state_map, psk_map, bad, dec_map}(Nonce_Delay_Reduction.R, Game3c)
  /\ NROc.RO.m{1} = Game3c.nonce_map{2}
) => //.

- by sim />.

- proc; inline*.
  sp; wp; if => //.
  by auto => />.
  
- proc; inline*.
  sp; wp; if => //.
  by sp; match =; auto => />.

- proc; inline*.
  sp; wp; if => //.
  sp; match = => //.
  + smt().
  move => si m1.
  sp; match = => //.
  + by auto.
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  swap {1} ^r1<$ @ ^if.
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => sr m1 m2.
  sp; match = => //.
  + by auto.
  move => nok.
  swap {1} ^r1<$ @ ^if.
  auto => />.
  smt(get_setE).

- by sim />.

- by sim />.

by auto => />.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 8: Game 3c to Game 3d - Remove checks for first sampling retrieval *)

lemma Hop8 bit &m: Pr[AKE_Game(Game3c, A).run(bit) @ &m : res] = Pr[AKE_Game(Game3d, A).run(bit) @ &m : res].
byequiv => //.
proc; inline.
call (: ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
      /\ (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map){2}
).

+ by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_send_msg1 => //.
  by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_send_msg2 => //.
  by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_send_msg3 => //.
  proc.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => si m1.
  sp; match = => //.
  + by auto.
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  rcondt {1} ^if.
  + auto => />.
    smt(mem_set).
  rcondt {1} ^if.
  + auto => />.
    smt(mem_set).
  by auto.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_send_fin => //.
  proc.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => sr m1 m2.
  sp; match = => //.
  + by auto.
  move => nok.
  rcondf {1} ^if.
  + auto => />.
    smt(mem_set).
  rcondf {1} ^if.
  + auto => />.
    smt(mem_set).
  by auto.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_reveal => //.
  by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad, nonce_map}(Game3c, Game3d)
  ) _ Game3d_inv_test => //.
  by sim />.

auto => />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 9: Game 3d to Game 4 - Compress nonce map *)

lemma Hop9 bit &m: Pr[AKE_Game(Game3d, A).run(bit) @ &m : res] = Pr[AKE_Game(Game4, A).run(bit) @ &m : res].
byequiv => //.
proc; inline.
call (: ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
      /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
      /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
          => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
            /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
      /\ (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map){1}
); try by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_send_msg1 => //.
  proc.
  sp; if => //.
  auto => />.
  smt(get_setE).
  
+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_send_msg2 => //.
  proc.
  sp; if => //.
  match = => //.
  + by auto.
  move => na.
  auto => />.
  smt(get_setE).

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_send_msg3 => //.
  proc.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => si m1.
  sp; match = => //.
  + by auto.
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  auto => />.
  smt(get_setE).

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_send_fin => //.
+ proc.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => sr m1 m2.
  sp; match = => //.
  + by auto.
  move => nok.
  auto => />.
  smt(get_setE).

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_reveal => //.
  by sim />.

+ conseq (: ={res}
          /\ ={b0, state_map, psk_map, dec_map, bad}(Game3d, Game4)
          /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){2}
          /\ (forall a b m1 m2 m3 n, Game4.prfkey_map{2}.[msg3_data a b m1 m2, m3] = Some n
              => Game3d.nonce_map{1}.[msg1_data a b, m1] = Some n.`1
                /\ Game3d.nonce_map{1}.[msg2_data a b m1, m2] = Some n.`2)
  ) Game3d_inv_test => //.
  by sim />.

auto => />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 10: Game 4 to Game 5 - Apply the PRF assumption. *)

local clone import DProd.ProdSampling with
  type t1 <- nonce,
  type t2 <- nonce
proof *.

lemma Hop10 bit &m:
    `|Pr[AKE_Game(Game4, A).run(bit) @ &m : res] - Pr[AKE_Game(Game5, A).run(bit) @ &m : res]|
  =
    `|Pr[PRF_Game(PRF_Oracles_0, PRF_Reduction(A)).run(bit) @ &m : res] - Pr[PRF_Game(PRF_Oracles_1, PRF_Reduction(A)).run(bit) @ &m : res]|.
proof.
do! congr.
+ byequiv => //.
  proc; inline*.
  wp.
  call (:
        ={b0, psk_map, state_map, dec_map, bad}(Game4, PRF_Reduction.R)
     /\ Game4.prfkey_map{1} = PRF_Oracles_common.key_map{2}
     /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game4.dec_map <=> (msg3_data a b m1 m2, m3) \in Game4.prfkey_map){1}
  ) => //.

  - by sim />.

  - proc.
    sp; if => //.
    auto => />.
    smt(get_setE).

  - proc.
    sp; if => //.
    match = => //.
    + by auto.
    move => na.
    auto => />.
    smt(get_setE).

  - proc; inline.
    sp; wp; if => //.
    sp; match = => //.
    + smt().
    move=> s m1.
    sp; match =.
    + smt().
    + by auto => />.
    move=> nb.
    seq 1 1 : (#pre /\ ={cok}); 1: by auto.
    sp; if=> //.
    rcondt{2} ^if.
    + auto=> />.
      smt().
    match Some {2} ^match.
    + by auto => />; smt(mem_set get_setE).
    outline {2} ^k0<$ ~ ProdSampling.S.sample.
    rewrite equiv [{2} ^ <@ ProdSampling.sample_sample2].
    inline.
    auto => />.
    smt(get_setE).

  - proc; inline*.
    sp; if=> //.
    sp; match = => //.
    + smt().
    move=> s m1 m2.
    sp; match =.
    + smt().
    + by auto=> />.
    move=> nok.
    match Some {2} ^match.
    + auto=> />.
      smt().
    auto => />.
    smt(get_setE).

    by sim />.

    by sim />.

  auto => />.
  smt(emptyE).

byequiv => //.
proc; inline *.
wp.
call (:
      ={b0, psk_map, state_map, dec_map, bad}(Game5, PRF_Reduction.R)
     /\ Game5.prfkey_map{1} = PRF_Oracles_common.key_map{2}
   /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game5.dec_map{1} <=> ((msg3_data a b m1 m2, m3), (a, b)) \in PRF_Oracles_1.cache{2})
   /\ (forall a b m1 m2 m3 k, PRF_Oracles_1.cache.[(msg3_data a b m1 m2, m3), (a, b)]{2} = Some k => Game5.key_map.[(a, m1), m2, m3]{1} = Some k)
   /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game5.dec_map <=> (msg3_data a b m1 m2, m3) \in Game5.prfkey_map){1}
)=> //.

- by sim />.

- proc; inline*.
  sp; wp; if => //.
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; wp; if => //.
  match = => //.
  + by auto => />.
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; wp; if => //.
  sp; match = => //.
  + smt().
  move => s m1.
  sp; match =.
  + smt().
  + by auto=> />.
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  rcondt{2} ^if.
  + auto => />.
    smt().
  match Some {2} ^match.
  + auto => />.
    smt(get_setE).
  outline {2} ^k0<$ ~ ProdSampling.S.sample.
  rewrite equiv [{2} ^ <@ ProdSampling.sample_sample2].
  inline.
  rcondt{2} ^if.
  + auto => />.
    smt().
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; if => //.
  sp; match = => //.
  + smt().
  move=> s m1 m2.
  sp; match =.
  + smt().
  + by auto => />.
  move => nok.
  match Some {2} ^match.
  + auto => />.
    smt().
  rcondf{2} ^if.
  + auto => />.
    smt().
  auto => />.
  smt().

- by sim />.

- by sim />.

auto => />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 11: Game 5 to Game 5a - Remove skeys from the state using key_map to retrieve. *)

local op clean3 (s : session_state) =
match s with
| IPending _ _ => s
| RPending _ _ _ => s
| Accepted tr k => Accepted tr witness
| Observed _ _ => s
| Aborted   => s
end.

local lemma clean3_trace s: trace (clean3 s) = trace s.
proof.
by case s=> //; move=> [] //=.
qed.

local lemma clean3_fresh h sml smr:
  (forall h, omap (fun (v: _ * _) => let (r, s) = v in (r, clean3 s)) sml.[h] = smr.[h]) =>
  fresh h sml <=> fresh h smr.
proof.
move=> eq_sm.
rewrite /fresh /observed_partners.
suff -> : partners h sml = partners h smr.
+ do! congr.
  rewrite fun_ext => h'.
  rewrite -(eq_sm h') //=.
  case: (sml.[h'])=> //.
  by move => [r' []] // [].
rewrite fsetP=> h'.
rewrite !mem_fdom !mem_filter /=.
rewrite !fmapP.
rewrite -(eq_sm h') -!(eq_sm h) /=.
case: (sml.[h'])=> //=.
move=> [r s].
have -> : exists y, (r, s) = y by exists (r, s).
have -> : exists y, (r, clean3 s) = y by exists (r, clean3 s).
case: (sml.[h])=> /=.
+ by rewrite clean3_trace.
move=> [r' s'] /=.
rewrite !clean3_trace.
by case s'.
qed.

lemma Hop11 bit &m:
    Pr[AKE_Game(Game5, A).run(bit) @ &m : res] = Pr[AKE_Game(Game5a, A).run(bit) @ &m : res].
proof.
byequiv => //.
proc; inline*.
call (:
    ={b0, psk_map, dec_map, bad, prfkey_map, key_map}(Game5, Game5a)
/\ (forall h, omap (fun v => let (r, s) = v in (r, clean3 s)) Game5.state_map.[h]{1} = Game5a.state_map.[h]{2})
/\ (forall h r tr k, Game5.state_map.[h] = Some (r, Accepted tr k) => Game5.key_map.[tr] = Some k){1}
/\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game5.dec_map => ((a, m1), m2, m3) \in Game5.key_map){1}
/\ (forall m, (forall ad , (ad, m) \notin Game5.dec_map) => (forall a m1 m2 m3, ((a, m1), m2, m3) \in Game5.key_map => m3 <> m)){1}
).

- by sim />.

- proc; inline*.
  sp; wp; if => //.
  + smt().
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; wp; if => //.
  + smt().
  match = => //.
  + auto => />.
    smt(get_setE).
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; wp; if => //.
  + smt().
  sp; match; 1..5: smt(); ~1: by auto.
  move => sl m1l sr m1r.
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if => //.
  + smt().
  sp; match; 1..5: smt(); ~2: by auto.
  move => sl m1l m2l sr m1r m2r.
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move => nok.
  auto => />.
  smt(get_setE).

- proc; inline.
  sp; if => //.
  + smt().
  sp; match; 1..5: smt(); ~3: by auto.
  move=> tr k tr' k'.
  if => //.
  + move => &1 &2 [] |> *.
    by rewrite (clean3_fresh h{2} Game5.state_map{1} Game5a.state_map{2}).
  auto=> /> &1 &2 + + eqsm invl a_in _.
  rewrite -(eqsm h{2}).
  move => *.
  split; 1: smt().
  split.
  move => h'.
  case (h' = h{2}) => [|hneq].
  + smt(get_set_sameE).
  rewrite !get_set_neqE // eqsm //.
  smt(get_setE).

- proc; inline.
  sp; if => //.
  + smt().
  sp; match; 1..5: smt(); ~3: by auto.
  move=> tr k tr' k'.
  if => //.
  + move => &1 &2 [] |> *.
    by rewrite (clean3_fresh h{2} Game5.state_map{1} Game5a.state_map{2}).
  if => //.
  + auto=> /> &1 &2 + + eqsm invl a_in _.
    rewrite -(eqsm h{2}).
    move => *.
    split; 1: smt().
    split.
    move => h'.
    case (h' = h{2}) => [|hneq].
    + smt(get_set_sameE).
    rewrite !get_set_neqE // eqsm //.
    smt(get_setE).
  auto => /> &1 &2 + + eqsm invl a_in _ _ _ ? ideal sk _.
  rewrite -(eqsm h{2}).
  move => stm1 stm2.
  split; 2: smt(get_setE).
  move => h'.
  case (h' = h{2}) => [|hneq].
  + smt(get_set_sameE).
  by rewrite !get_set_neqE // eqsm.

auto => />.
by smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 12: Game 5a to Game 5b - Delaying sampling of the keys to reveal/test *)

lemma Hop12 &m b:
    Pr[AKE_Game(Game5a, A).run(b) @ &m : res] = Pr[AKE_Game(Game5b, A).run(b) @ &m : res].
proof.
byequiv => //.
proc*.

(* Proof for the real side *)
transitivity* {1} { r <@ KROc.MainD(Key_Delay_Reduction(A), KROc.RO).distinguish(b); }.
+ inline*; wp.
  call(: ={b0, state_map, psk_map, dec_map, bad, prfkey_map}(Game5a, Key_Delay_Reduction.R)
         /\ Game5a.key_map{1} = KROc.RO.m{2}
         /\ (forall h r tr k, Game5a.state_map.[h] = Some (r, Accepted tr k) => tr \in Game5a.key_map){1}
         /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in Game5a.dec_map => ((a, m1), m2, m3) \in Game5a.key_map){1}
         /\ (forall m1 m2 m3, (forall ad, (ad, m3) \notin Game5a.dec_map) => (m1, m2, m3) \notin Game5a.key_map){1}
  ).

  - by sim />.

  - proc; inline.
    sp; wp; if => //.
    auto => />.
    smt(mem_set get_setE).

  - proc; inline.
    sp; wp; if => //.
    match = => //.
    + auto => />.
      smt(get_setE).
    auto => />.
    smt(mem_set get_setE).

  - proc; inline.
    sp; wp; if => //.
    sp; match = => //.
    + smt().
    move=> s m1.
    sp; match =.
    + smt().
    + auto => />.
      smt(get_setE).
    move => nb.
    seq 1 1 : (#pre /\ ={cok}); 1: by auto.
    sp; if => //.
    rcondt {2} ^if.
    + by auto => /#.
    wp.
    rnd.
    wp; rnd{2}.
    auto => />.
    smt(mem_set get_setE).

  - proc; inline.
    sp; if => //.
    sp; match = => //.
    + smt().
    move => s m1 m2.
    sp; match = => //.
    + auto => />.
      smt(get_setE).
    move => nok.
    auto => />.
    smt(get_setE).

  - proc; inline.
    sp; if => //.
    sp 1 1; match = => //.
    + smt().
    move => tr k'.
    if => //.
    auto => />.
    smt(get_setE).

  - proc; inline.
    sp; if => //.
    sp 1 1; match = => //.
    + smt().
    move => tr k'.
    if => //.
    rcondf{2} ^if.
    + auto => />.
      smt(get_setE).
    kill{2} ^r0<$; 1: islossless.
    by sp; if; auto; smt(get_setE).
    
  auto => />.
  smt(emptyE).

rewrite equiv [{1} 1 (KROc.FullEager.RO_LRO (Key_Delay_Reduction(A)) _)]; 1: by move=> _; exact dskey_ll.
+ auto => />.
inline; wp.
sim (: ={state_map, psk_map, dec_map, bad, prfkey_map}(Key_Delay_Reduction.R, Game5b)
     /\ Key_Delay_Reduction.R.b0{1} = Game5b.b0{2}
     /\ KROc.RO.m{1} = Game5b.key_map{2}
).

- proc; inline.
  sp; if => //.
  sp.
  match = => //.
  + smt().
  move => tr k'.
  if => //.
  sp; seq 1 1 : (#pre /\ r0{1} = k'{!2}); 1: by auto.
  if => //.
  + by sp; if; auto; smt(get_setE).
  by sp; if; auto; smt(get_setE).

- proc; inline.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => tr k'.
  if => //.
  auto => />.
  smt(get_setE).

- proc; inline.
  sp; if => //.
  sp; match = => //.
  + smt().
  move => s m1.
  sp; match = => //.
  + by auto.
  move => nb.
  seq 1 1 : (#pre /\ ={cok}); 1: by auto.
  sp; if => //.
  wp; rnd{1}.
  by auto => />.

by auto.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 13: Game 5b to Game 3c - Remove checks for new key samplings *)


lemma Hop13 &m b:
    Pr[AKE_Game(Game5b, A).run(b) @ &m : res] = Pr[AKE_Game(Game5c, A).run(b) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
     /\ (Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map){2}
).

- by sim />.

- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_send_msg1 => //.
  by sim />.
- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_send_msg2 => //.
  by sim />.
- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_send_msg3 => //.
  by sim />.
- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_send_fin => //.
  by sim />.

- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_reveal => //.
  proc; inline.
  sp; if => //.
  sp 1 1; match = => //.
  + smt().
  move=> tr k'.
  if => //.
  seq 1 1 : (={k'} /\ #pre); 1: by auto => />.
  if{1}.
  + by auto => /#.
  exfalso.
  move => &1 &2 [#] />.
  move => smai2 smai1. 
  move => uniq_pi ss_log_rp ss_log_ip ss_log_acc ss_log_obs sk_obs ai_in _ obs_ps.
  case (tr \in Game5c.key_map{2}) => // ^ tr_in_skm.
  move => /(sk_obs tr) [a' i' r sk smai'].
  have smai : Game5c.state_map.[h]{2} = Some (r{!2}, Accepted tr k') by smt().
  case (r = r{!2}).
  + have := uniq_pi tr.`1.`2 r h{2} (Accepted tr k') (a', i') (Observed tr sk).
    smt().
  move => neq_role.
  have bj_partner : (a', i') \in partners h{2} Game5c.state_map{2}.
  + by rewrite /get_partners mem_fdom mem_filter domE smai' smai /= eq_sym.
  have // : (a', i') \in observed_partners h{2} Game5c.state_map{2}.
  + by rewrite /get_observed_partners in_filter /= smai' /(\o).
  rewrite fcard_eq0 in obs_ps.
  by rewrite obs_ps in_fset0.

- conseq (: ={res}
     /\ ={state_map, psk_map, b0, dec_map, bad, prfkey_map, key_map}(Game5b, Game5c)
  ) _ Game5c_inv_test => //.
  proc; inline*.
  sp; if => //.
  sp 1 1; match = => //.
  + smt().
  move=> tr k'.
  if => //.
  seq 1 1 : (={k'} /\ #pre); 1: by auto => />.
  if{1}.
  + by sp; if; auto => /#.
  exfalso.
  move => &1 &2 [#] />.
  move => smai2 smai1. 
  move => uniq_pi ss_log_rp ss_log_ip ss_log_acc ss_log_obs sk_obs ai_in _ obs_ps.
  case (tr \in Game5c.key_map{2}) => // ^ tr_in_skm.
  move => /(sk_obs tr) [a' i' r sk smai'].
  have smai : Game5c.state_map.[h]{2} = Some (r{!2}, Accepted tr k') by smt().
  case (r = r{!2}).
  + have := uniq_pi tr.`1.`2 r h{2} (Accepted tr k') (a', i') (Observed tr sk).
    smt().
  move => neq_role.
  have bj_partner : (a', i') \in partners h{2} Game5c.state_map{2}.
  + by rewrite /get_partners mem_fdom mem_filter domE smai' smai /= eq_sym.
  have // : (a', i') \in observed_partners h{2} Game5c.state_map{2}.
  + by rewrite /get_observed_partners in_filter /= smai' /(\o).
  rewrite fcard_eq0 in obs_ps.
  by rewrite obs_ps in_fset0.

auto => />.
smt(emptyE mem_empty).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Hop 14: Game 5c to Game 5c - flip the bit *)

lemma Hop14 &m:
    Pr[AKE_Game(Game5c, A).run(false) @ &m : res] = Pr[AKE_Game(Game5c, A).run(true) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: ={state_map, psk_map, dec_map, bad, prfkey_map}(Game5c, Game5c)
     /\ !Game5c.b0{1} /\ Game5c.b0{2}
     /\ (forall h, h \in Game5c.key_map{1} <=> h \in Game5c.key_map{2})
); try by sim />.

+ proc; inline*.
  sp; if => //.
  sp; match = => //.
  + smt().
  move=> tr k'.
  if => //.
  auto => />.
  smt(get_setE).

+ proc; inline*.
  sp; if => //.
  sp; match = => //.
  + smt().
  move=> tr k'.
  if => //.
  rcondt{1} ^if; 1: by auto => />.
  rcondf{2} ^if; 1: by auto => />.
  auto => />.
  smt(get_setE).

by auto => />.
qed.

lemma Security &m: `| Pr[AKE_Game(AKE_Oracles(KAP1), A).run(false) @ &m : res] - Pr[AKE_Game(AKE_Oracles(KAP1), A).run(true) @ &m : res]|
  <= `|Pr[AEAD_Game(AEAD_Oracles_0, AEAD_Reduction(A)).run(false) @ &m : res] - Pr[AEAD_Game(AEAD_Oracles_1, AEAD_Reduction(A)).run(false) @ &m : res]|
      + `|Pr[AEAD_Game(AEAD_Oracles_0, AEAD_Reduction(A)).run(true) @ &m : res] - Pr[AEAD_Game(AEAD_Oracles_1, AEAD_Reduction(A)).run(true) @ &m : res]|
      + `|Pr[PRF_Game(PRF_Oracles_0, PRF_Reduction(A)).run(false) @ &m : res] - Pr[PRF_Game(PRF_Oracles_1, PRF_Reduction(A)).run(false) @ &m : res]|
      + `|Pr[PRF_Game(PRF_Oracles_0, PRF_Reduction(A)).run(true) @ &m : res] - Pr[PRF_Game(PRF_Oracles_1, PRF_Reduction(A)).run(true) @ &m : res]|
      + ((q_m1 + q_m2 + q_m3) * (q_m1 + q_m2 + q_m3 - 1))%r * p_max dctxt.
proof.
do rewrite Hop1 Hop2.
do rewrite -Hop3 -Hop10.
do rewrite -Hop9 -Hop8 -Hop7 -Hop6 -Hop5.
do rewrite Hop11 Hop12 Hop13.
apply (ler_trans
        (`|Pr[AKE_Game(Game1a, A).run(false) @ &m : res] - Pr[AKE_Game(Game2, A).run(false) @ &m : res]| +
         `|Pr[AKE_Game(Game1a, A).run(true) @ &m : res] - Pr[AKE_Game(Game2, A).run(true) @ &m : res]| +
         `|Pr[AKE_Game(Game2, A).run(false) @ &m : res] - Pr[AKE_Game(Game2, A).run(true) @ &m : res]|)).
+ smt(ler_norm_add).
have : `|Pr[AKE_Game(Game2, A).run(false) @ &m : res] -
  Pr[AKE_Game(Game2, A).run(true) @ &m : res]| <=
`|Pr[AKE_Game(Game3, A).run(false) @ &m : res] -
  Pr[AKE_Game(Game5c, A).run(false) @ &m : res]| +
`|Pr[AKE_Game(Game3, A).run(true) @ &m : res] -
  Pr[AKE_Game(Game5c, A).run(true) @ &m : res]| +
  ((q_m1 + q_m2 + q_m3) * (q_m1 + q_m2 + q_m3 - 1))%r * p_max dctxt; last by smt(ler_add2l).
apply (ler_trans
        (`|Pr[AKE_Game(Game3, A).run(false) @ &m : res] - Pr[AKE_Game(Game3, A).run(true) @ &m : res]| +
         ((q_m1 + q_m2 + q_m3) * (q_m1 + q_m2 + q_m3 - 1))%r * p_max dctxt
)); 1: by smt(ler_norm_add Hop4 Hop4_bound).
rewrite ler_add2r.
smt(ler_norm_add Hop14).
qed.

end section.

print Security.
