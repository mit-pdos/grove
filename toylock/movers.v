From iris.algebra Require Import excl agree gmap lib.excl_auth gmultiset.
From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants ghost_var.
From iris.heap_lang Require Export notation lang.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Export tactics.

Class netG Σ := NetG {
  net_msgsG :> inG Σ (authR (gmultisetUR valO));
  net_ghostG :> ghost_varG Σ (gmultiset val);
}.

Section movers.
  Context `{!heapG Σ, !netG Σ}.

  Definition message := positive.
  
  Definition network_state := gmultiset val.
  
  Axiom own_network : forall (γ:gname) (s:network_state), iProp Σ.
  Axiom own_network_timeless : forall (γ:gname) (s:network_state), Timeless (own_network γ s).
  Existing Instance own_network_timeless.

  Parameter send_pkt : val.
  Axiom send_axiom : forall s E γ (v : val) (ns:network_state),
      {{{ own_network γ ns }}}
        send_pkt v @ s; E
      {{{ RET #(); own_network γ (ns ∪ {[ v ]}) }}}.

  Axiom send_pkt_atomic : forall a v, Atomic a (send_pkt v).
  Existing Instance send_pkt_atomic.

  Parameter recv_pkt : val.
  Axiom recv_axiom : forall s E γ (ns:network_state),
      {{{ own_network γ ns }}}
        recv_pkt #() @ s; E
      {{{ (v:val), RET v; (⌜v = NONEV⌝ ∗ own_network γ ns )
                          ∨ (∃ m, ⌜m ∈ ns ∧ v = SOMEV m⌝ ∗ own_network γ (ns ∖ {[m]}))
      }}}.

  Axiom recv_pkt_atomic : forall a v, Atomic a (recv_pkt v).
  Existing Instance recv_pkt_atomic.

  (* Assume well-known network ghost names. *)
  Context (γpnet γgdiff γgnet : gname).
  Let N := nroot .@ "mover_network".

  Definition network_inv : iProp Σ :=
    ∃ net_phys net_ghost,
      own_network γpnet net_phys ∗
      own γgdiff (● net_ghost ⋅ ◯ net_phys) ∗
      ghost_var γgnet (1/2) net_ghost.
  Definition network_ctx : iProp Σ := inv N network_inv.

  Notation own_gnetwork ns := (ghost_var γgnet (1/2) ns).

  Lemma recv_mkdiff (net_phys net_ghost : gmultiset val) m :
    own γgdiff (● net_ghost ⋅ ◯ net_phys) ==∗
    own γgdiff (● net_ghost ⋅ ◯ (net_phys ∖ {[ m ]})) ∗ own γgdiff (◯ {[ m ]}).
  Proof. Admitted.

  Lemma recv_phys :
    network_ctx -∗
    {{{ True }}}
      recv_pkt #()
    {{{ (v:val), RET v; (⌜v = NONEV⌝ ∨
      (∃ (m:val), ⌜v = SOMEV m⌝ ∗ own γgdiff (◯ {[ m ]}))) }}}.
  Proof.
    iIntros "#Hctx" (Φ) "_ !# HΦ".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iApply (recv_axiom with "Hpnet"). iIntros "!>" (v) "[Hret|Hret]".
    { iDestruct "Hret" as (->) "Hpnet". iIntros "!>". iSplitR "HΦ".
      - iNext. iExists _, _. iFrame.
      - iApply "HΦ". eauto. }
    iDestruct "Hret" as (m [Hm ->]) "Hpnet".
    iMod (recv_mkdiff with "Hgdiff") as "[Hgdiff Hgtok]".
    iIntros "!>". iSplitR "HΦ Hgtok".
    - iNext. iExists _, _. iFrame.
    - iApply "HΦ". eauto.
  Qed.

  Lemma recv_elimdiff (net_phys net_ghost : gmultiset val) m :
    own γgdiff (● net_ghost ⋅ ◯ net_phys) -∗ own γgdiff (◯ {[ m ]}) ==∗
    ⌜m ∈ net_ghost⌝ ∗ own γgdiff (● (net_ghost ∖ {[ m ]}) ⋅ ◯ net_phys).
  Proof. Admitted.

  Lemma recv_log E ns m :
    ↑N ⊆ E →
    network_ctx -∗
    own γgdiff (◯ {[ m ]}) -∗
    own_gnetwork ns -∗
    |={E}=> ⌜m ∈ ns⌝ ∗ own_gnetwork (ns ∖ {[ m ]}).
  Proof.
    iIntros (?) "#Hctx Hgtok Hgnetc".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iDestruct (ghost_var_agree with "Hgnetc Hgnet") as %->.
    iMod (ghost_var_update_halves with "Hgnetc Hgnet") as "[Hgnetc Hgnet]".
    iMod (recv_elimdiff with "Hgdiff Hgtok") as (?) "Hgdiff".
    iIntros "!>". iSplitR "Hgnetc".
    - iNext. iExists _, _. iFrame.
    - eauto.
  Qed.

  Lemma send_log E ns m :
    ↑N ⊆ E →
    network_ctx -∗
    own_gnetwork ns -∗
    |={E}=> own γgdiff (◯ {[ m ]}) ∗ own_gnetwork (ns ∪ {[ m ]}).
  Proof. Admitted.

  Lemma send_phys (m : val) :
    network_ctx -∗
    {{{ own γgdiff (◯ {[ m ]}) }}}
      send_pkt m
    {{{ RET #(); True }}}.
  Proof. Admitted.


End movers.
