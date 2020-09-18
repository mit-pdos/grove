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
            inG Σ (excl_authR (prodO boolO ZO))
           }.

Definition channelN (ch : val) := nroot .@ "channel" .@ ch.
Definition dlockN (s: val) := nroot .@ "channel" .@ s.

Definition is_pkt (p:val) (m:message) : iProp Σ :=
  match m with
  | {|epoch := e; grant := g|} => ⌜p = (PairV #e #g)⌝%I
  end.

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
    {{{ v, RET v; is_pkt v m ∗is_channel γ (removelast s) }}}.
 *)

(* recv with no-duplication (even the same packet being sent multiple times gets deduped) *)
Axiom recv_axiom : forall γ (s:network_state) (s':network_state) (id:node_id),
    {{{ is_network γ s }}}
      recv_pkt #id
    {{{ v, RET v; ∃ m, ⌜m ∈ s ∧ m.(dst) = id⌝ ∗ is_pkt v m ∗is_network γ (s ∖ {[m]}) }}} .

Definition new_pkt : val :=
  λ: "epoch" "msg",
  let: "p" := ("epoch", "msg") in
  "p".

Definition is_distributed_lock_node (s:val) (γs: gmap node_id gname) : iProp Σ
  := (∃ (l:loc) (e:Z) (g:bool) (id:node_id) (γ:gname),
         ⌜s = #l⌝ ∗ (l ↦ (#g, #e, #id)%I)
               ∗(⌜lookup id γs = Some γ⌝) ∗ own γ (●E (g, e))).

Definition is_distributed_lock_inv (γs : gmap node_id gname) P : iProp Σ :=
  ( ([∗ map] γ ∈ γs, (∃ e:Z, own γ (◯E (false, e)))%I) ∗ P )
  ∨
  (∃ id0 γ0,
      ⌜γs !! id0 = Some γ0⌝ ∗
        ([∗ map] id ↦ γ ∈ γs,
                            (⌜id = id0⌝ ∗(∃ e:Z, own γ0 (◯E (true, e))) ) ∨ (⌜id ≠ id0⌝ ∗ (∃ e:Z, own γ (◯E (false, e)))%I) )
           (* ∧ all packets in network are unacceptable *)
  ).

Let N := nroot .@ "toylock".

Definition is_distributed_lock (γs : gmap node_id gname) P : iProp Σ :=
  inv N (is_distributed_lock_inv γs P).

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

Lemma node_grant_spec η ns P γs s:
  {{{ is_network η ns ∗ is_distributed_lock_node s γs ∗ is_distributed_lock γs P  ∗ P }}}
    node_grant s
  {{{ RET #(); is_distributed_lock_node s γs }}}.
Proof.
  iIntros (Φ) "(Hn & Hs & #HI & HP) Post".
  iDestruct "Hs" as (l e g id γ) "(Hs & Hl & Hmap & Hγ)".
  iDestruct "Hs" as %->.
  iDestruct "Hmap" as %Hmap.
  wp_lam. wp_load. wp_let.
  wp_pures.
  destruct g; wp_pures.
  - wp_lam. wp_let. wp_pures.
    wp_bind (_ <- _)%E.
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
      iDestruct "Hinv" as "[Hholder Hinv]".
      iDestruct "Hholder" as "[Hholder|Hholder]".
      ++ iDestruct "Hholder" as "[_ Hholder]".
         iDestruct "Hholder" as (e) "Hholder".
         

      {
        iExFalso.
        iDestruct "Hholder" as "[Hbad _]".
        iRevert "Hbad".
        iPureIntro. auto.
      }
      
      iDestruct ("Hinv" $! id γ with "[]") as "Hinv".
         { done. }
         iDestruct "Hinv" as (e') "Hinv".
         iExFalso.
         iCombine "Hγ Hinv" as "Hγ".
         iDestruct (own_valid with "Hγ") as %Hvalid.
         iPureIntro.
         Check excl_auth_agree.
         apply (excl_auth_agree (true, e) (false, e')) in Hvalid.
         elim Hvalid.
         discriminate.
       + iDestruct "Hinv" as (id' γ' e') "Hinv".
         Print big_opL.
         iDestruct "Hinv" as "(H1 & Hγ' & #Hids)".
         iAssert (⌜id' = id⌝%I with ()) as "Hid".
         {
           iApply ("Hids" $! id γ e).
         }



    wp_store.
    Check send_axiom.
    wp_apply ((send_axiom η (#(e + 1), #true) (Build_message (e+1) true id%Z (id + 1)%Z) ns) with "[Hn]").
    { iFrame. auto. }
    iIntros "Hn".

    iApply "Post".
    unfold is_distributed_lock_node.
    iExists l.
    iExists (e+1)%Z.
    iExists false.
    iExists id.
    iExists γ.
    iFrame.
    rewrite -fupd_frame_l.
    iSplit; first done.
    rewrite -fupd_frame_l.
    iSplit; first done.
    unfold is_distributed_lock.
    Check inv_alloc.
    Check excl_auth_update.
    -- iSpecialize ("Hinv" $! id).
       iDestruct "Hinv" as ">Hinv".
    -- iDestruct ("Hinv" $! id γ with "[]") as "HH".
  -

         "HI" as "Hinv" "HClose". admit.

    Check fupd_wp.
    iAssert (|={⊤}=> own γ (●E (false, (e + 1)%Z)))%I as "HHH".
    -- iInv "HI" as "Hinv" "HClose". admit.
    -- iDestruct "HHH" as "HHH".
      
    iMod fupd_intro_mask' as "HH".
    iApply (fupd_elim ⊤ ⊤ ⊤).
    iInv "HI" as "Hinv" "HClose".
    

Lemma node_grant_spec s P γs:
  {{{ is_distributed_lock_node s γs ∗ is_distributed_lock_node γs P }}}
    node_accept s
  {{{ ∃b, RET #b; is_distributed_lock_node s γs ∗ ((b = false) ∨ (b = true ∗ P)) }}}

Lemma node_grant_spec (s s1 s2:val) P :
  {{{ is_distributed_lock s s1 s2 P }}}
    node_grant s
    {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#HDLockInv Post".
  wp_lam.
  unfold is_distributed_lock.
  iDestruct "HDLockInv" as "[Hs Hothers]".
  iDestruct "Hs" as (l) "(Hl & HInv)".
  iDestruct "Hl" as %->.
  Print invG.
  wp_bind (! _)%E.
  iInv (dlockN #l) as (e g rch sch) "HI" "HClose".
  iDestruct "HI" as "[HI | HI]".
  - iDestruct "HI" as "[HI HII]". wp_load.
    iMod ("HClose" with "[]").
Admitted.

End toylock_code.
