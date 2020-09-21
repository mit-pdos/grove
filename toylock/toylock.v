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
    
  Definition network_state := gmultiset message.

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

Axiom own_network : forall (γ:gname) (s:network_state), iProp Σ.

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
    {{{ own_network γ s ∗ is_pkt v m }}}
      send_pkt v
    {{{ RET #(); own_network γ (s ∪ {[ m ]}) }}}.

Axiom send_pkt_atomic : forall a v, Atomic a (send_pkt v).
Existing Instance send_pkt_atomic.

(* Recv axiom for synchronous network
Axiom recv_axiom : forall m γ (s:network_state) (s':network_state) (id:node_id),
    ((option_map last (lookup id s)) = Some(Some(m))) ->
    {{{ is_channel γ s }}}
      recv_pkt #id
    {{{ v, is_pkt v m ∗is_channel γ (removelast s) }}}.
 *)

(* *)

Check (InjLV #()).
(* recv with no-duplication (even the same packet being sent multiple times gets deduped) *)
Axiom recv_axiom : forall s E γ (ns:network_state) (id:node_id),
    {{{ ▷own_network γ ns }}}
      recv_pkt #id @ s; E
      {{{ (v:val), RET v; (⌜v = NONEV⌝ ∗own_network γ ns )
                    ∨ (∃ m (p:val), ⌜m ∈ ns ∧ m.(dst) = id ∧ v = SOMEV p⌝ ∗ is_pkt p m ∗own_network γ (ns ∖ {[m]}))
      }}}.

Axiom recv_pkt_atomic : forall a v, Atomic a (recv_pkt v).
Existing Instance recv_pkt_atomic.

Definition new_pkt : val :=
  λ: "epoch" "msg",
  let: "p" := ("epoch", "msg") in
  "p".

Definition own_distributed_lock_node (s:val) (γs: gmap node_id gname) ρ: iProp Σ
  := (∃ (l:loc) (e:Z) (g:bool) (id:node_id) (γ:gname),
         ⌜s = #l⌝∗⌜lookup id γs = Some γ⌝
               ∗(l ↦ (#g, #e, #id)%I)
                ∗ own γ (●E (g, e))
               ∗(⌜g = true⌝∗own ρ (◯E (id)) ∨ ⌜g = false⌝)
     ).

Definition distributed_lock_inv (γs : gmap node_id gname) ρ P η : iProp Σ :=
  ∃ ns, own_network η ns ∗
  (
  ( ∃ m, ⌜ns ⊆ {[ m ]}⌝ ∗ ([∗ map] γ ∈ γs, (∃ e:Z, ⌜(e < m.(epoch))%Z⌝ ∗ own γ (◯E (false, e)))%I) ∗ P
            ∗own ρ (●E m.(dst) ⋅ ◯E m.(dst) )
  )
  ∨
  (∃ id0 γ0 e0,
      ⌜γs !! id0 = Some γ0⌝
        ∗ (⌜ns = ∅⌝)
        ∗ own ρ (●E (id0))
        ∗([∗ map] id ↦ γ ∈ (delete id0 γs),
                (∃ e:Z, ⌜(e < e0)%Z⌝ ∗own γ (◯E (false, e)))%I
          )
    ∗(∃ e:Z, own γ0 (◯E (true, e0)))
  )
  ).

Let N := nroot .@ "toylock".

Definition is_distributed_lock (γs : gmap node_id gname) ρ P η: iProp Σ :=
  inv N (distributed_lock_inv γs ρ P η).

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

(*
Lemma recv_lemma η id P γs ρ:
  {{{ is_distributed_lock γs ρ P η }}}
    recv_pkt #id

  {{{ (v:val), RET v; (⌜v = NONEV⌝ ∨ (∃ m (p:val), ⌜m ∈ ns ∧ m.(dst) = id ∧ v = SOMEV p⌝ ∗ is_pkt p m) )
    }}}.
*)

Lemma node_accept_spec η s P γs ρ:
  {{{ own_distributed_lock_node s γs ρ ∗ is_distributed_lock γs ρ P η }}}
    node_accept s
  {{{ b, RET #b; own_distributed_lock_node s γs ρ ∗ (⌜b = false⌝ ∨ (⌜b = true⌝ ∗ P)) }}}.
Proof.
  iIntros (Φ) "(Hnode & #Hsys) Post".
  iDestruct "Hnode" as (l e g id γ -> Hid) "(Hl & Hγ & Hρfrag)".
  wp_lam.
  wp_load.
  wp_pures.
  Check recv_axiom.
  Check send_axiom.
  wp_bind (recv_pkt #id)%E.
  iInv N as "Hnet" "HClose".
  Check bi.later_exist.
  iDestruct (bi.later_exist with "Hnet") as "Hnet".
  iDestruct "Hnet" as (ns) "(Hnet & InvRest)".
  wp_apply (recv_axiom _ _ η ns id with "Hnet").
  iIntros (p) "Hnet".
  iDestruct "Hnet" as "[Hnet|Hnet]".
  + (* returned NONE *)
    iDestruct "Hnet" as (->) "Hnet".
    iMod ("HClose" with "[InvRest Hnet]") as "_". { iExists ns. iFrame. }
    iModIntro.
    wp_pures.
    iApply "Post".
    iSplitL "Hl Hγ Hρfrag". { iExists l, e, g, id, γ. iFrame. iSplit; done. }
    iLeft; done.
  + iDestruct "Hnet" as (m pkt [Hm [_ ->]] ->) "Hη".
    iMod ("HClose" with "[InvRest Hη]") as "_".
    { (* Closing invariant in case that a packet is removed *)
      iNext. admit.
    }
    iModIntro.
    wp_pures.
    destruct bool_decide as [HH|HH].
  - (* Message epoch is higher *)
    wp_pures. wp_bind (#l <- _)%E.
    iInv N as "Hinv" "HClose".
    wp_store.
    iDestruct "Hinv" as (ns') "[Hnet [Hinv|Hinv]]".
    -- iDestruct "Hinv" as (m') "(#Hns & Hmap & HP & Hρ)".
       iDestruct ((big_sepM_delete _ γs id γ) with "Hmap") as "(Hγfrag & Hmap)"; first done.
       iDestruct "Hγfrag" as (e' He') "Hγfrag".
        iMod (own_update_2 _ _ _ (●E (true, m.(epoch)) ⋅ ◯E (true, m.(epoch))) with "Hγ Hγfrag") as "[Hγ Hγfrag]"; first by apply excl_auth_update.
        iDestruct "Hρ" as "[Hρ Hρfrag']".
        iMod ("HClose" with "[Hγfrag Hmap Hρfrag' Hnet]").
        {
          iNext. iExists ns'. iFrame. iRight.
          iExists id, γ, m.(epoch). auto.
          iSplit; first done.
        }
    (* Update ghost state and sho *)
  - (* Message epoch is lower *)


    
  - (* recv returns a packet *)
    iDestruct "Hpkt" as (m pkt [Hmsg [Hdst ->]] ->) "Hnet".
    wp_pures.
    destruct bool_decide as [HH|HH].
    + (* successfully received packet *)
      wp_pures.
      wp_bind (#l <- _)%E.
      iInv N as "HI" "HClose".
      wp_store.
      unfold distributed_lock_inv.
      iDestruct "HI" as (ns) "[Hnet [HI|HI]]".
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

Lemma node_grant_spec η ns P γs ρ s:
  {{{ own_network η ns ∗ is_distributed_lock_node s γs ρ ∗ is_distributed_lock γs ρ P  ∗ P }}}
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
