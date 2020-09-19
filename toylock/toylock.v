From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl agree lib.excl_auth.
From stdpp Require Import gmap.

Require Import ListSet.
Require Import ZModulo.


Class lockG Σ := lock_G :> inG Σ (exclR unitR).
Print unitR.

Section toylock_code.

Parameter send_pkt : val.
Parameter recv_pkt : val.

  Definition node_id := Z.

  Record message :=
    Build_message
      {
        epoch: Z;
        grant: bool;
        src: node_id;
        dst: node_id;
      }.

  Print gset.
  Global Instance message_eq_dec : EqDecision message.
  Proof.
    solve_decision.
  Qed.

  Global Instance message_countable : Countable message.
  Proof.
    Check inj_countable.
    refine (inj_countable' (λ l,
                            match l with
                            | Build_message e g s d => (e, g, s, d)
                            end
                           )
                           (λ l,
                            match l with
                            | (e, g, s, d) => {| epoch:=e; grant:=g; src:=s; dst:=d |}
                            end
                           ) _
                           ); by intros [].
  Qed.
    
  Definition network_state := gset message.

  Canonical Structure networkRA := leibnizO network_state.

  Print boolO.
  Definition node_state : Type := bool * Z.
  Canonical Structure nodeRA := leibnizO node_state.

  Context `{heapG Σ, lockG Σ, inG Σ (agreeR networkRA),
            inG Σ (exclR unitR),
            inG Σ (excl_authR (prodO boolO ZO)),
            inG Σ (excl_authR ZO)
           }.

Definition channelN (ch : val) := nroot .@ "channel" .@ ch.
Definition dlockN (s: val) := nroot .@ "channel" .@ s.

Definition is_pkt (p:val) (m:message) : iProp Σ :=
  ⌜p = (PairV #(m.(epoch)) #(m.(grant)))⌝%I.

Axiom is_network : forall (γ:gname) (s:network_state), iProp Σ.

Print network_state.
(* Send axiom for synchronous network *)
(*
Axiom send_axiom : forall γ v (m:message) (s:network_state),
    {{{ is_channel γ s ∗ is_pkt v m }}}
      send_pkt v
    {{{ RET #(); is_channel γ (partial_alter (λ l, match l with
                                                    | None => Some(m :: nil)
                                                    | Some(l) => Some(m :: l)
                                                    end)
                                            m.(dst) s) }}}.
*)

Axiom send_axiom : forall γ v (m:message) (s:network_state),
    {{{ is_network γ s ∗ is_pkt v m }}}
      send_pkt v
    {{{ RET #(); is_network γ (s ∪ {[ m ]}) }}}.

(* Recv axiom for synchronous network
Axiom recv_axiom : forall m γ (s:network_state) (s':network_state) (id:node_id),
    ((option_map last (lookup id s)) = Some(Some(m))) ->
    {{{ is_channel γ s }}}
      recv_pkt #id
    {{{ v, is_pkt v m ∗is_channel γ (removelast s) }}}.
 *)

Check (InjLV #()).
(* recv with no-duplication (even the same packet being sent multiple times gets deduped) *)
Axiom recv_axiom : forall γ (s:network_state) (id:node_id),
    {{{ is_network γ s }}}
      recv_pkt #id
      {{{ (v:val), RET v; (is_network γ s ∗ (⌜v = NONEV⌝))
                    ∨ (∃ m (p:val), ⌜m ∈ s ∧ m.(dst) = id ∧ v = SOMEV p⌝ ∗ is_pkt p m ∗is_network γ (s ∖ {[m]}))
      }}}.

Definition new_pkt : val :=
  λ: "epoch" "msg",
  let: "p" := ("epoch", "msg") in
  "p".

Definition is_distributed_lock_node (s:val) (γs: gmap node_id gname) ρ: iProp Σ
  := (∃ (l:loc) (e:Z) (g:bool) (id:node_id) (γ:gname),
         ⌜s = #l⌝ ∗ (l ↦ (#g, #e, #id)%I)
               ∗(⌜lookup id γs = Some γ⌝) ∗ own γ (●E (g, e))
               ∗(⌜g = true⌝∗own ρ (◯E (id)) ∨ ⌜g = false⌝)
     ).

Definition is_distributed_lock_inv (γs : gmap node_id gname) ρ P : iProp Σ :=
  ( ([∗ map] γ ∈ γs, (∃ e:Z, own γ (◯E (false, e)))%I) ∗ P
        ∗(∃ id0, own ρ (●E id0 ⋅ ◯E id0) )
  )
  ∨
  (∃ id0 γ0,
      ⌜γs !! id0 = Some γ0⌝
        ∗ own ρ (●E (id0))
        ∗([∗ map] id ↦ γ ∈ (delete id0 γs),
                (∃ e:Z, own γ (◯E (false, e)))%I
          )
        ∗(∃ e:Z, own γ0 (◯E (true, e)))
  (* ∧ all packets in network are unacceptable *)
  ).

Let N := nroot .@ "toylock".

Definition is_distributed_lock (γs : gmap node_id gname) ρ P : iProp Σ :=
  inv N (is_distributed_lock_inv γs ρ P).

Definition node_grant : val :=
  λ: "s",
  let: "n" := !"s" in
  if: Fst $ Fst "n" = #true then (* if s.held == true { *)
    let: "e" := (Snd $ Fst "n") + #1 in
    let: "transfer_pkt" := (new_pkt "e" #true) in
    "s" <- (#false, "e", (Snd "n")) ;;
    send_pkt ("transfer_pkt")
  else
    #().

Definition node_accept : val :=
  λ: "s",
  let: "n" := !"s" in
  let: "p" := recv_pkt (Snd "n") in
  match: "p" with
    NONE => #false
  | SOME "pkt" =>
    if: (Snd $ Fst "n") < (Fst "pkt") then
      "s" <- (#true, Fst "pkt", Snd "n") ;;
      #true
    else
      #false
  end.


Lemma ea_update γ a b c:
    own γ (●E a ⋅ ◯E b) -∗ |==> own γ (●E c ⋅ ◯E c).
Proof.
  apply own_update.
  apply excl_auth_update.
Qed.

Lemma node_accept_spec η ns s P γs ρ:
  {{{ is_network η ns ∗
       is_distributed_lock_node s γs ρ ∗ is_distributed_lock γs ρ P }}}
    node_accept s
    {{{ b, RET #b; is_distributed_lock_node s γs ρ ∗ (⌜b = false⌝ ∨ (⌜b = true⌝ ∗ P)) }}}.
  iIntros (Φ) "(Hnet & Hnode & Hsys) Post".
  iDestruct "Hnode" as (l e g id γ) "(Hs & Hl & #Hid & Hγ & Hρ)".
  iDestruct "Hs" as %->.
  wp_lam.
  wp_load.
  wp_pures.
  Check recv_axiom.
  Check send_axiom.
  wp_bind (recv_pkt #id)%E.
  wp_apply (recv_axiom η ns id with "Hnet").
  iIntros (p) "[Hpkt|Hpkt]".
  - (* recv returned NONEV *)
    iDestruct "Hpkt" as "(Hnet & Hpkt)".
    iDestruct "Hpkt" as %->.
    wp_let. wp_match.
    iApply "Post".
    iSplitL "Hl Hγ Hρ".
    + iExists l, e, g, id, γ. iFrame. iSplit; done.
    + iLeft. done.
  - (* recv returns a packet *)
    iDestruct "Hpkt" as (m pkt) "(Hmsg & Hpkt & Hnet)".
    unfold is_pkt.
    iDestruct "Hmsg" as "(Hmsg & Hdst & Hp)".
    iDestruct "Hp" as %->.
    wp_pures.
    iDestruct "Hpkt" as %->.
    wp_pures.
    assert (exists me , m.(epoch) = me) as Hme.
    {
      exists (epoch m). done.
    }
    destruct Hme as [me Hme].
    rewrite -> Hme.
    case bool_decide.
    + (* successfully received packet *)
      wp_pures.
      wp_bind (#l <- _)%E.
      iInv N as "HI" "HClose".
      wp_store.
      unfold is_distributed_lock_inv.
      iDestruct "HI" as "[HI|HI]".
      -- (* Correct invariant case, all nodes do not have lock *)
        iClear "Hρ".
        iDestruct "Hid" as %Hid.
        iDestruct "HI" as "(Hmap & HP & Hρ)".
        iDestruct ((big_sepM_delete _ γs id γ) with "Hmap") as "(Hγfrag & Hmap)"; first done.
        iDestruct "Hγfrag" as (e') "Hγfrag".
        Check own_update_2.
        iMod (own_update_2 _ _ _ (●E (true, me) ⋅ ◯E (true, me)) with "Hγ Hγfrag") as "[Hγ Hγfrag]"; first by apply excl_auth_update.
        iDestruct "Hρ" as (id_ρ) "Hρ".
        iMod (own_update _ _ (●E id ⋅ ◯E id) with "Hρ") as "[Hρ Hρfrag]"; first by apply excl_auth_update.
        iMod ("HClose" with "[Hmap Hρ Hγfrag]").
        {
          iNext. iRight. iExists id, γ. iSplit; first done.
          iFrame. iExists me. done.
        }
        iModIntro. wp_seq.
        iApply "Post".
        iSplitL "Hl Hγ Hρfrag".
        {
          iExists l, me, true, id, γ.
          iSplit; first done. iFrame.
          iSplit; first done.
          iLeft. iFrame. done.
        }
        iRight. iFrame. done.
      -- admit.
    + wp_pures.
      iApply "Post".
      iSplitL "Hl Hγ Hρ".
      { iExists l, e, g, id, γ. iFrame. iSplit; done. }
      iLeft. done.
Admitted.

Admitted.

Lemma node_grant_spec η ns P γs ρ s:
  {{{ is_network η ns ∗ is_distributed_lock_node s γs ρ ∗ is_distributed_lock γs ρ P  ∗ P }}}
    node_grant s
  {{{ RET #(); is_distributed_lock_node s γs ρ }}}.
Proof.
  iIntros (Φ) "(Hn & Hs & #HI & HP) Post".
  iDestruct "Hs" as (l e g id γ) "(Hs & Hl & Hmap & Hγ & Hρfrag)".
  iDestruct "Hs" as %->.
  iDestruct "Hmap" as %Hmap.
  wp_lam. wp_load. wp_let.
  wp_pures.
  destruct g; wp_pures.
  - wp_lam. wp_let. wp_pures.
    wp_bind (_ <- _)%E.
    iDestruct "Hρfrag" as "[[_ Hρfrag] | %]"; last done.
    iInv "HI" as "Hinv" "HClose".
    -- wp_store.
       iDestruct "Hinv" as "[[Hinv HinvP ] |Hinv]".
    + iDestruct (big_opM_delete _ γs id γ) as "HinvProp"; first done.
      iDestruct ("HinvProp" with "Hinv") as "[Hγfrag Hinv]".
      iClear "HinvProp".
      iDestruct "Hγfrag" as (e') "Hγfrag".
      iCombine "Hγ Hγfrag" as "Hγ".
      iExFalso.
      iDestruct (own_valid with "Hγ") as %Hvalid.
      iPureIntro.
      apply (excl_auth_agree (true, e) (false, e')) in Hvalid.
      elim Hvalid. discriminate.

    + iDestruct "Hinv" as (holder_id holder_γ) "(Hholder & Hinv)".
      iDestruct "Hholder" as %Hholder.
      rewrite (big_opM_delete _ γs holder_id holder_γ); last done.
      iDestruct "Hinv" as "(Hρ & Hholder & Hinv)".
      iDestruct "Hholder" as "[Hholder|Hholder]".
      ++ iDestruct "Hholder" as "[_ Hholder]".
         iDestruct "Hholder" as (e') "Hholder".
         iCombine "Hρ Hρfrag" as "Hρ".
         iDestruct (own_valid with "Hρ") as %Hvalid.
         apply (excl_auth_agree holder_id id) in Hvalid.
         rewrite <- Hvalid in Hmap.
         elim Hvalid.
         assert (holder_γ = γ) as Hγ_eq.
         {
           enough (Some γ = Some holder_γ).
           injection H5 as Hdone. done.
           rewrite <- Hholder.
           rewrite <- Hmap.
           done.
         }
         elim Hγ_eq.
         iCombine "Hγ Hholder" as "Hγ".
         iDestruct (own_valid with "Hγ") as %Hvalid2.
         apply (excl_auth_agree) in Hvalid2.
         destruct Hvalid2 as [_ Hvalid2]. simpl in Hvalid2. elim Hvalid2.

         Check ◯E (false, e).
         Check ea_update.
         iMod (own_update _ _  (●E (false, (e+1)%Z) ⋅ ◯E (false, (e+1)%Z)) with "Hγ") as "Hγ"; first by apply excl_auth_update.
         
         iDestruct (big_sepM_mono _ (λ k x, (∃ e0 : Z, own x (◯E (false, e0)))%I) _ with "Hinv") as "Hinv".
         {
           intros. simpl. iStartProof.
           iIntros "Hk".
           iDestruct "Hk" as "[(% & _) |Hk]".
           {
             iExFalso.
             Check lookup_delete.
             rewrite -> H6 in H5.
             rewrite -> (lookup_delete _ _) in H5.
             discriminate.
           }
           iDestruct "Hk" as "(Hk & He)".
           iDestruct "He" as (e0) "He".
           iExists e0. auto.
         }
         iDestruct "Hγ" as "[Hγ Hγfrag]".
         iDestruct (big_sepM_delete _ γs holder_id holder_γ with "[Hinv Hγfrag]") as "Hinv".
          { auto. }
          { iFrame.
          iExists (e+1)%Z; iFrame.
          }
          simpl.

          iMod ("HClose" with "[Hρ HP Hinv]").
          {
            iNext. iLeft. iFrame. iExists holder_id. iFrame.
          }
          iModIntro.
          wp_seq.
          wp_apply ((send_axiom η (#(e + 1), #true) (Build_message (e+1) true id%Z (id + 1)%Z) ns) with "[Hn]").
          {
            iFrame. auto.
          }
          
          iIntros "_".
          iApply "Post".
          iExists l, (e+1)%Z, false, holder_id, holder_γ.
          iFrame.
          iSplit; first done.
          iSplit; first done.

          iRight.
          done.

      ++
        iExFalso.
        iDestruct "Hholder" as "[Hbad _]".
        iRevert "Hbad".
        iPureIntro. auto.

  - iApply "Post".
    iExists l, e, false, id, γ.
    iFrame. auto.
Qed.


End toylock_code.
