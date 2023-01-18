From Coq Require Import Bool.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq Require Import String.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
Require Import Lia.


Section Auction.
  Context `{Base : ChainBase}.

  Set Nonrecursive Elimination Schemes.
  
  Inductive AuctionState :=
  | not_sold_yet : AuctionState
  | sold : Address -> AuctionState.

  Record Setup :=
    setup {
        setup_item : string;
        setup_duration : nat;
        setup_start_price : Amount;
        setup_minimum_raise : Amount;
      }.
  
  Record State :=
    build_state {
        auction_state : AuctionState;
        auction_seller : Address;
        auction_item : string;
        auction_duration : nat;
        auction_minimum_raise : Amount;
        auction_current_price : Amount;
        auction_highest_bidder : option Address;
        auction_creation_slot : nat;
      }.

  Definition Error : Type := nat.
  Definition default_error: Error := 1%nat.

  Inductive Msg :=
  | bid
  | finalize.

  MetaCoq Run (make_setters State).
  
  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<bid, finalize>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<setup>.
    
    Global Instance AuctionState_serializable : Serializable AuctionState :=
      Derive Serializable AuctionState_rect<not_sold_yet, sold>.
    
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.
  
  End Serialization.

  Local Open Scope Z.
  Definition init
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    let seller := ctx_from ctx in
    let item := setup_item setup in
    let start_price := setup_start_price setup in
    let duration := setup_duration setup in
    let minimum_raise := setup_minimum_raise setup in
    (* Ensure seller does not transfer during initialization *)
    do if ctx.(ctx_amount) =? 0 then Ok tt else Err default_error;
    Ok (build_state
          not_sold_yet  (* Item is not sold initially *)
          seller        (* Seller is the creator of the auction *)
          item          (* Item to be sold, represented as a string *)
          duration      (* The number of time slots, auction is running *)
          minimum_raise (* Minimum riase to accept and over bid *)
          start_price   (* Initial price *)
          None          (* Initial highest bidder *)
          chain.(current_slot) (* Slot of contract initialization *)
      ).
  
  Definition place_bid
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    : result (State * list ActionBody) Error :=
    let seller := auction_seller state in
    let price := auction_current_price state in
    let min_raise := auction_minimum_raise state in
    let bid_amount := ctx_amount ctx in
    let curr_slot := current_slot chain in
    let start_slot := auction_creation_slot state in
    let dur := auction_duration state in
    let bidder := ctx_from ctx in
    (* Ensure bidder is not a contract *)
    do if address_is_contract bidder
       then Err default_error
       else Ok tt;
    (* Ensure the seller does not bid *)
    do if (bidder =? seller)%address
       then Err default_error
       else Ok tt;
    (* Ensure auction has not ended *)
    do if (start_slot + dur <=? curr_slot)%nat
       then Ok tt
       else Err default_error;
    (* Ensure auction is still active. *)
    do match auction_state state with
       | not_sold_yet => Ok tt
       | _ => Err default_error
       end;
    (* Ensure new bid raises by at least the minimum raise amount. *)
    do if bid_amount <? price + min_raise
       then Err default_error
       else Ok tt;
    (* If there was a previous highest bidder, return the bid. *)
    let action_list :=
      match auction_highest_bidder state with
      | None => []
      | Some addr => [act_transfer addr price]
      end in
    (* Update the state with the new highest bid and bidder *)
    let new_state :=
      state<| auction_current_price  := bid_amount  |>
           <| auction_highest_bidder := Some bidder |>
    in
    Ok (new_state, action_list).

  Definition finalize_auction
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    : result (State * list ActionBody) Error :=
    let amount := ctx.(ctx_amount) in
    let curr_slot := current_slot chain in
    let start_slot := auction_creation_slot state in
    let dur := auction_duration state in
    (* Ensure no currency is passed to finalize *)
    do if amount =? 0
       then Ok tt
       else Err default_error;
    (* Ensure the auction has ended *)
    do if (curr_slot <? start_slot + dur)%nat
       then Ok tt
       else Err default_error;
    (* Ensure the auction has not been finalized *)
    do match auction_state state with
       | not_sold_yet => Ok tt
       | _ => Err default_error
       end;
    (* TODO: How to deal with unsold item? *)
    do bidder <- result_of_option (auction_highest_bidder state) default_error;
    let new_state := state<| auction_state := sold bidder |> in
    Ok (new_state, [act_transfer (auction_seller state) (auction_current_price state)]).
  
  Definition receive
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    (* Placing a bid. *)
    | Some bid => place_bid chain ctx state
    (* Finalizing Auction *)
    | Some finalize => finalize_auction chain ctx state
    (* Empty Message *)
    | None => Err default_error
    end.
  
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.
  
End Auction.


Section Theories.
  Context `{Base : ChainBase}.
  Open Scope Z.

  Ltac just_do_it arg :=
    cbn in *; destruct_match in arg; try congruence.
  
  Ltac unfold_receive arg :=
    unfold receive in arg;
    unfold place_bid in arg;
    unfold finalize_auction in arg.

  Lemma no_self_calls bstate caddr:
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (auction_highest_bidder cstate <> Some caddr /\
         auction_seller cstate <> caddr /\
         Forall (fun abody => match abody with
                           | act_transfer to _ => (to =? caddr)%address = false
                           | _ => False
                           end) (outgoing_acts bstate caddr)).
  Proof with auto.
    contract_induction;
      intros; (try apply IH in H as H'); cbn in *; auto.
    - repeat split.
      + destruct result.
        unfold init in init_some.
        just_do_it init_some.
      + instantiate (DeployFacts := fun _ ctx => ctx.(ctx_from) <> ctx.(ctx_contract_address)).
        unfold DeployFacts in *.
        destruct setup0; destruct result; cbn in *.
        just_do_it init_some.
      + auto.
    - destruct IH as [IH1 [IH2 IH3]]; split;
      inversion IH3; auto...
    - destruct IH as [IH1 [IH2 IH3]]; split;
      try apply Forall_app; try split.
      + unfold receive in receive_some.
        do 2 just_do_it receive_some...
        * repeat just_do_it receive_some.
          ** inversion receive_some; cbn in *.
             intro.
             inversion H; congruence.
          ** inversion receive_some; cbn in *.
             congruence.
        * do 4 just_do_it receive_some.
          inversion receive_some; cbn in *...
      + unfold receive in receive_some; cbn in *.
        do 2 just_do_it receive_some;
        auto; repeat just_do_it receive_some; inversion receive_some...
      + apply Forall_app; split...
        unfold receive in receive_some.
        do 2 just_do_it receive_some; try (inversion receive_some; auto; fail);
        repeat just_do_it receive_some; inversion receive_some;
        auto;
        apply Forall_cons;
        auto;
        apply address_eq_ne;
        intro;
        congruence.
    - destruct IH as [IH1 [IH2 IH3]];
        repeat split; 
        inversion IH3;
        destruct head; subst; auto;
        destruct action_facts as [A1 [A2 A3]]; subst; easy.
    - destruct IH as [IH1 [IH2 IH3]]; repeat split...
      now rewrite <- perm.
    - solve_facts.
      apply undeployed_contract_no_out_queue in not_deployed...
      + rewrite queue_prev in *.
        apply Forall_inv in not_deployed.
        destruct_address_eq; try congruence.
        intro.
        subst.
        cbn in *.
        apply n...
      + now constructor.
  Qed.

  Check ChainTrace.

  Ltac solve_no_self_call_facts :=
    solve_facts;
    match goal with
    | [ msg : option SerializedValue,
          from_reachable: ChainTrace empty_state ?bstate_from,
            queue_prev: chain_state_queue ?bstate_from = _ |- _ <> ?to_addr ] =>
        apply trace_reachable in from_reachable;
        pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption)) as all;
        destruct all as [? [? [? [? all]]]];
        unfold outgoing_acts in *;
        rewrite queue_prev in *;
        cbn in all;
        destruct_address_eq; cbn in *; auto;
        inversion_clear all as [|? ? hd _];
        destruct msg;
        [contradiction
        | rewrite address_eq_refl in hd;
          congruence]
    | _ => fail
    end.
  
  Lemma no_highest_bidder_zero_balance bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (cstate.(auction_state) = not_sold_yet ->
                cstate.(auction_highest_bidder) = None ->
                env_account_balances bstate caddr = sumZ act_body_amount (outgoing_acts bstate caddr)).
  Proof with cbn in *.
    contract_induction; intros...
    - eauto.
    - unfold init in init_some.
      remember (ctx_amount ctx =? 0).
      symmetry in Heqb.
      destruct b; try congruence.
      now rewrite Z.eqb_eq in Heqb.
    - pose proof (IH H H0).
      rewrite Z.sub_move_r.
      now rewrite Z.add_comm.
    - rewrite sumZ_app.
      unfold_receive receive_some.
      repeat just_do_it receive_some;
        destruct prev_state;
        destruct new_state;
        inversion receive_some;
        now cbn in *.
    - instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *; easy.
    - rewrite <- perm; eauto.
    - solve_no_self_call_facts.
  Qed.

  Lemma not_sold_contract_balance bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (forall amt addr, cstate.(auction_state) = not_sold_yet ->
                     cstate.(auction_current_price) = amt ->
                     ( (* New highest bidder *)
                       (cstate.(auction_highest_bidder) = Some addr ->
                        env_account_balances bstate caddr = amt + (sumZ act_body_amount (outgoing_acts bstate caddr))) /\
                       (* No highest bidder *)
                       (cstate.(auction_highest_bidder) = None ->
                        env_account_balances bstate caddr = sumZ act_body_amount (outgoing_acts bstate caddr)))).
    Proof with cbn in *.
    contract_induction; intros...
    (* Deploy *)
    - eauto.
    (* Init *)
    - split; intros; unfold init in *.
      (* Some new bidder *)
      + destruct result; just_do_it init_some.
      (* No new bidder *)
      + remember (ctx_amount ctx =? 0).
        symmetry in Heqb.
        destruct b; try congruence.
        now rewrite Z.eqb_eq in Heqb.
    (* Outgoing transfer *)
    - split; intros...
      (* Some new bidder *)
      + rewrite Z.sub_move_r.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm (sumZ act_body_amount out_acts) (act_body_amount out_act)).
        eapply IH; eauto.
      (* No new bidder *)
      + pose proof (IH amt addr H H0) as [IH1 IH2].
        pose proof (IH2 H1).
        rewrite Z.sub_move_r.
        now rewrite Z.add_comm.
    (* Receive Nonrecursive *)
    - split; intros...
      (* Some new bidder *)
      + rewrite sumZ_app.
        destruct prev_state.
        destruct new_state.
        unfold_receive receive_some...
        repeat just_do_it receive_some;
          inversion receive_some; try easy; cbn in *;
          subst;
          rewrite Z.add_comm;
          rewrite <- Z.sub_move_r;
          [rewrite Z.add_0_r|];
          now eapply IH.
      (* No new bidder *)
      + rewrite sumZ_app.
        unfold_receive receive_some.
        repeat just_do_it receive_some;
          destruct prev_state;
          destruct new_state;
          inversion receive_some;
          now cbn in *.
    (* Receive Recursive *)
    - instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx).
        subst CallFacts; cbn in *; easy.
    (* Permutations *)  
    - split; intros; rewrite <- perm; now eapply IH.
    (* Facts *)
    - solve_no_self_call_facts.
  Qed.
  
  Lemma not_sold_contract_balance_full bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (forall amt addr, cstate.(auction_state) = not_sold_yet ->
                     cstate.(auction_current_price) = amt ->
                     ( (* New highest bidder *)
                       (cstate.(auction_highest_bidder) = Some addr ->
                        env_account_balances bstate caddr = amt + (sumZ act_body_amount (outgoing_acts bstate caddr))) /\
                       (* No highest bidder *)
                       (cstate.(auction_highest_bidder) = None ->
                        env_account_balances bstate caddr = sumZ act_body_amount (outgoing_acts bstate caddr)))) /\
        (* All money is accounted for when sold *)
        (forall addr, cstate.(auction_state) = sold addr ->
                 env_account_balances bstate caddr = sumZ act_body_amount (outgoing_acts bstate caddr)).
  Proof with cbn in *.
    contract_induction; intros...
    (* Deploy *)
    - eauto.
    (* Init *)
    - repeat split; intros; unfold init in *.
      (* Some new bidder *)
      + destruct result; just_do_it init_some.
      (* No new bidder *)
      + remember (ctx_amount ctx =? 0).
        symmetry in Heqb.
        destruct b; try congruence.
        now rewrite Z.eqb_eq in Heqb.
      (* Auction has ended *)
      + destruct result; just_do_it init_some.
    (* Outgoing transfer *)
    - repeat split; intros...
      (* Some new bidder *)
      + rewrite Z.sub_move_r.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm (sumZ act_body_amount out_acts) (act_body_amount out_act)).
        now eapply IH.
      (* No new bidder *)
      + destruct IH as [IH _].
        pose proof (IH amt addr H H0) as [_ IH'].
        pose proof (IH' H1).
        rewrite Z.sub_move_r.
        now rewrite Z.add_comm.
      (* Auction ends *)
      + destruct IH as [_ IH].
        pose proof (IH addr H).
        rewrite Z.sub_move_r.
        now rewrite Z.add_comm.
    (* Receive Nonrecursive *)
    - repeat split; intros...
      (* Some new bidder *)
      + destruct IH as [IH _].
        rewrite sumZ_app.
        destruct prev_state.
        destruct new_state.
        unfold_receive receive_some...
        repeat just_do_it receive_some;
          inversion receive_some; try easy; cbn in *;
          subst;
          rewrite Z.add_comm;
          rewrite <- Z.sub_move_r;
          [rewrite Z.add_0_r|];
          now eapply IH.
      (* No new bidder *)
      + destruct IH as [IH _].
        rewrite sumZ_app.
        unfold_receive receive_some.
        repeat just_do_it receive_some;
          destruct prev_state;
          destruct new_state;
          inversion receive_some;
          now cbn in *.
      (* Auction ends *)
      + unfold_receive receive_some.
        remember (ctx_amount ctx =? 0).
        symmetry in Heqb.
        destruct b;
          [ rewrite Z.eqb_eq in Heqb; rewrite sumZ_app |];
          destruct prev_state;
          destruct new_state;
          destruct auction_highest_bidder0;
          destruct auction_state0;
          repeat just_do_it receive_some;
          inversion receive_some; try easy...
        rewrite <- Heqb.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm (ctx_amount ctx) (sumZ act_body_amount prev_out_queue)).
        rewrite Z.add_assoc.
        rewrite <- Z.sub_move_r.
        rewrite <- H6.
        now eapply IH.
    (* Receive Recursive *)
    - instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *; easy.
    (* Permutations *)  
    - split;
        [ destruct IH as [IH _]
        | destruct IH as [_ IH]];
        intros; rewrite <- perm; now eapply IH.
    (* Facts *)
    - solve_no_self_call_facts.
  Qed.
        
  (* Contract does not get stuck unless intended *)
  (** ** Bid correct *)
  (* In no reachable state is the seller the highest bidder *)
  Lemma seller_cannot_bid_on_own_auction bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        auction_highest_bidder cstate <> Some (auction_seller cstate).
  Proof with auto.
    contract_induction; intros; cbn in *...
    - destruct result.
      cbn in *.
      inversion init_some.
      just_do_it init_some.
    - unfold_receive receive_some;
      destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state));
        repeat just_do_it receive_some;
       cbn in receive_some; inversion receive_some; cbn in *; auto;
        intro; apply n; cbn in *; inversion H...
    - unfold_receive receive_some;
      destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state));
        repeat just_do_it receive_some;
        cbn in receive_some; inversion receive_some; cbn in *; auto;
        intro; apply n; cbn in *; inversion H...
    - solve_facts.
  Qed.
  
  (* Outbidding invokes a transfer to previous highest bidder *)
  Lemma place_bid_refund :
    forall (chain : Chain)
      (ctx : ContractCallContext)
      (state state' : State)
      (addr addr' : Address)
      (alist : list ActionBody),
      state.(auction_highest_bidder) = Some addr ->
      state'.(auction_highest_bidder) = Some addr' ->
      receive chain ctx state (Some bid) = Ok (state', alist) ->
      alist = [act_transfer addr state.(auction_current_price)].
    Proof.
      intros; unfold_receive H1; repeat just_do_it H1.
    Qed.

(* Naïve one-step version first
   Maybe look into something like:
   "if the auction is finished in blockstate a and some blockstate b
    is reachable from a. Then the auction is still finished in state b"
*) 
  Lemma sold_state_is_final_one_step :
    forall (chain : Chain)
      (ctx : ContractCallContext)
      (state : Auction.State)
      (msg : option Auction.Msg)
      (winner : Address)
      (state' : Auction.State)
      (alist : list ActionBody),
      auction_state state = sold winner ->
      receive chain ctx state msg = Ok (state', alist) ->
      auction_state state' = sold winner.
  Proof.
    intros;
      destruct state;
      unfold receive in H0;
      vm_compute in H; subst;
      repeat just_do_it H0;
      now inversion H0.
  Qed.

  (* Seller is immutable *)
  Lemma seller_is_immutable :
    forall (chain : Chain)
      (ctx : ContractCallContext)
      (state state' : Auction.State)
      (msg : option Auction.Msg)
      (alist : list ActionBody),
      receive chain ctx state msg = Ok (state', alist) ->
      auction_seller state = auction_seller state'.
  Proof.
    intros;
      destruct state;
      unfold receive in H;
      vm_compute in H; subst;
      repeat just_do_it H;
      now inversion H.
  Qed.
  
  Theorem only_to_previous_bidder_and_no_more_money chain ctx prev msg new acts :
    receive chain ctx prev msg = Ok (new, acts) ->
    Forall (fun abody => match abody with
                           | act_transfer to amount => match auction_highest_bidder prev with
                                                      | Some bidder => to = bidder \/ to = auction_seller prev
                                                      | None => True
                                                      end
                           | _ => True
                           end) acts.
  Proof.
    intros receive_some.
    unfold receive in receive_some.
    destruct_match in receive_some; cbn in *; try congruence.
    destruct_match in receive_some; cbn in *; try (inversion receive_some; easy).
    - destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      inversion receive_some.
      destruct (auction_highest_bidder prev); last easy.
      apply list.Forall_singleton. easy.
    - destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      destruct_match in receive_some; cbn in *; try congruence.
      inversion receive_some.
      apply list.Forall_singleton. destruct (auction_highest_bidder prev); easy.
  Qed.

  Definition state_constant `{A : Type} (f : State -> A) := forall chain ctx prev msg new acts,
    receive chain ctx prev msg = Ok (new, acts) ->
    f prev = f new.

  Lemma seller_constant : state_constant (fun s => s.(auction_seller)).
  Proof.
    unfold state_constant. intros.
    rename H into receive_some.
    unfold receive in receive_some.
    destruct_match in receive_some; cbn in *; try congruence.
    destruct_match in receive_some; cbn in *; repeat destruct_match in receive_some; cbn in *; try congruence; inversion receive_some; reflexivity.
  Qed.

  Lemma item_constant : state_constant (fun s => s.(auction_item)).
  Proof.
    unfold state_constant.
    intros. rename H into receive_some.
    unfold receive in receive_some.
    repeat just_do_it receive_some; inversion receive_some; auto.
  Qed.

  (* What's for the bidder?

     As far as the bidder concerns, if he made an bid, and the current bidder is not him,
     there should be a transfer to him with the exact same amount.

     A weaker one is that, the amount that bidder transfers in equals the amount the contract
     transfers back, if the bidder is not the current highest bidder, else adding the current
     highest bid.
   *)

  Definition call_to_addr_amount {Msg} (call : ContractCallInfo Msg) :=
    (call_from call, call_amount call).

  Definition call_from_list {Msg} from (inc_calls : list (ContractCallInfo Msg)) :=
    filter (fun c => (c.(call_from) =? from)%address) inc_calls.

  Definition sumZ_call {Msg} (caller : Address) (inc_calls : list (ContractCallInfo Msg)) :=
    sumZ (fun c => c.(call_amount)) (call_from_list caller inc_calls).

  Definition sumZ_tx (to : Address) (txs : list Tx) :=
    sumZ (fun tx => tx.(tx_amount)) (filter (fun tx => (tx.(tx_to) =? to)%address) txs).

  Definition is_act_transfer_to destination (act : ActionBody) :=
    match act with
    | act_transfer to amount => (to =? destination)%address
    | act_call to amount msg => (to =? destination)%address
    | act_deploy amount c _ => false
    end.

  Definition sumZ_act (to : Address) (acts : list ActionBody) :=
    sumZ act_body_amount (filter (fun act => is_act_transfer_to to act) acts).

  Lemma act_only_transfer bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    Forall (fun act => match act with
                    | act_transfer to amount => True
                    | act_call to amount msg => False
                    | act_deploy amount c _ => False
                    end
      ) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; cbn in *; eauto.
    - apply Forall_cons_iff in IH. destruct IH.
      destruct out_act; try easy.
    - unfold receive in receive_some. repeat just_do_it receive_some.
      all: inversion receive_some; apply Forall_app; auto.
    - apply Forall_cons_iff in IH. destruct IH.
      unfold receive in receive_some. destruct head; try contradiction.
      repeat just_do_it receive_some; inversion receive_some; apply Forall_app; auto.
    - now rewrite <- perm.
    - solve_facts.
  Qed.

  Theorem highest_bidder_fact chain ctx cstate new_state new_acts bidder :
    receive chain ctx cstate (Some bid) = Ok (new_state, new_acts) ->
    auction_highest_bidder new_state = Some bidder ->
    ctx_from ctx = bidder /\ ctx_amount ctx = auction_current_price new_state.
  Proof.
    intros receive_some. unfold receive in receive_some.
    do 6 just_do_it receive_some; inversion receive_some; cbn; easy.
  Qed.

  Theorem highest_bidder_not_seller bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate, contract_state bstate caddr = Some cstate /\
    Some (auction_seller cstate) <> (auction_highest_bidder cstate).
  Proof.
    contract_induction; intros; cbn in *; eauto.
    - repeat just_do_it init_some. now inversion init_some.
    - pose proof (seller_constant _ _ _ _ _ _ receive_some). cbn in H.
      unfold receive in receive_some. do 2 just_do_it receive_some.
      + destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state)).
        repeat just_do_it receive_some. repeat just_do_it receive_some; inversion receive_some; subst; now cbn in *.
      + repeat just_do_it receive_some; inversion receive_some; subst; now cbn in *.
    - instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx).
      now unfold CallFacts in facts.
    - solve_no_self_call_facts.
  Qed.

  Theorem highest_bidder_bid_before bstate caddr bidder (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate inc_calls, incoming_calls Msg trace caddr = Some inc_calls /\
                        contract_state bstate caddr = Some cstate /\
                        (
                          auction_highest_bidder cstate = Some bidder ->
                          Exists (fun c => c.(call_from) = bidder /\ c.(call_amount) = auction_current_price cstate)
                                 inc_calls
                        ).
  Proof.
    contract_induction; intros; cbn in *; eauto.
    - just_do_it init_some. inversion init_some. subst. now cbn in H.
    - unfold receive in receive_some. just_do_it receive_some. destruct m.
      + pose proof (highest_bidder_fact chain ctx prev_state new_state new_acts bidder).
        cbn in H0. apply H0 in receive_some. destruct receive_some. subst. now apply Exists_cons_hd. easy.
      + repeat just_do_it receive_some. inversion receive_some. cbn. rewrite <- H1 in H. cbn in H.
        apply IH in H. now apply Exists_cons_tl.
    - unfold receive in receive_some. just_do_it receive_some. destruct m.
      + pose proof (highest_bidder_fact chain ctx prev_state new_state new_acts bidder).
        cbn in H0. apply H0 in receive_some. destruct receive_some. subst. now apply Exists_cons_hd. easy.
      + repeat just_do_it receive_some. inversion receive_some. cbn. rewrite <- H1 in H. cbn in H.
        apply IH in H. now apply Exists_cons_tl.
      (* could get around by no recursive call *)
    - solve_facts.
  Qed.

  Theorem bidder_transfer_even bstate caddr bidder (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate inc_calls, incoming_calls Msg trace caddr = Some inc_calls /\
                        contract_state bstate caddr = Some cstate /\
                        Forall (fun act => match act with
                                        | act_transfer to amount => True
                                        | act_call to amount msg => False
                                        | act_deploy amount c _ => False
                                        end
                          ) (outgoing_acts bstate caddr) /\
                        (
                          cstate.(auction_highest_bidder) <> Some bidder ->
                          cstate.(auction_seller) <> bidder ->
                          sumZ_call bidder inc_calls = sumZ_tx bidder (outgoing_txs trace caddr) +
                                                         sumZ_act bidder (outgoing_acts bstate caddr)
                        ) /\
                        (
                          cstate.(auction_highest_bidder) = Some bidder ->
                          sumZ_call bidder inc_calls = sumZ_tx bidder (outgoing_txs trace caddr) +
                                                         sumZ_act bidder (outgoing_acts bstate caddr) +
                                                         cstate.(auction_current_price)
                        ).
  Proof.
    contract_induction; intros; try cbn in receive_some; try destruct IH; try split; try split; try intros; eauto.
    - destruct H0. now apply H0 in H1.
    - destruct H0. now apply H2 in H1.
    - cbn in init_some. just_do_it init_some. inversion init_some. now subst.
    - apply Forall_cons_iff in H. now destruct H.
    - destruct out_act.
      + apply H0 in H1. rewrite H1. destruct tx_act_match as (? & ? & ?). subst.
        cbn. destruct (tx_to tx =? bidder)%address; unfold sumZ_tx, sumZ_act; cbn; lia.
        easy.
      + apply Forall_cons_iff in H. destruct H as [[]].
      + apply Forall_cons_iff in H. destruct H as [[]].
    - destruct out_act.
      + apply H0 in H1. rewrite H1. destruct tx_act_match as (? & ? & ?). subst.
        cbn. destruct (tx_to tx =? bidder)%address; unfold sumZ_tx, sumZ_act; cbn; lia.
      + apply Forall_cons_iff in H. destruct H as [[]].
      + apply Forall_cons_iff in H. destruct H as [[]].
    - unfold receive in receive_some. repeat just_do_it receive_some.
      all: inversion receive_some; apply Forall_app; auto.
    - cbn. destruct (address_eqb_spec (ctx_from ctx) bidder); cbn.
      + unfold receive in receive_some. do 2 just_do_it receive_some.
        * repeat just_do_it receive_some; inversion receive_some; subst; try contradiction.
        * remember (ctx_amount ctx =? 0). destruct b; last inversion receive_some.
          repeat just_do_it receive_some; inversion receive_some; subst.
          cbn in *. destruct H0. pose proof (H0 H1 H2). apply address_eq_ne in H2. rewrite H2.
          apply eq_sym in Heqb. apply Z.eqb_eq in Heqb. rewrite Heqb. unfold sumZ_call,call_from_list in H4.
          rewrite H4. cbn. unfold sumZ_act. reflexivity.
      + destruct (auction_highest_bidder prev_state) eqn:?.
        * destruct (address_eqb_spec a bidder).
          {
            assert (Some a = Some bidder); first easy.
            apply H0 in H3. unfold sumZ_call, call_from_list in H3. rewrite H3.
            rewrite e in Heqo.
            destruct msg; last easy. destruct m.
            - repeat just_do_it receive_some. inversion receive_some. subst.
              cbn. inversion Heqo. rewrite address_eq_refl. cbn. now unfold sumZ_act.
            - repeat just_do_it receive_some. inversion receive_some. subst. cbn in *. contradiction.
          }
          {
            assert (Some a <> Some bidder); first easy.
            apply H0 in H3. unfold sumZ_call, call_from_list in H3. rewrite H3.
            destruct msg; last easy. destruct m.
            - repeat just_do_it receive_some. inversion receive_some. subst.
              cbn. inversion Heqo. rewrite (address_eq_ne _ _ n0). now unfold sumZ_act.
            - repeat just_do_it receive_some. inversion receive_some. subst. cbn in *.
              rewrite (address_eq_ne _ _ H2). now unfold sumZ_act.
            - now apply seller_constant in receive_some.
          }
        * assert (None <> Some bidder); first easy.
          apply H0 in H3. unfold sumZ_call, call_from_list in H3. rewrite H3.
          unfold receive in receive_some. repeat just_do_it receive_some; inversion receive_some; subst; cbn in *.
          easy.
          rewrite (address_eq_ne _ _ H2). easy.
          now apply seller_constant in receive_some.
    - cbn. destruct (address_eqb_spec (ctx_from ctx) bidder); cbn.
      + destruct (auction_highest_bidder prev_state) eqn:?.
        * destruct (address_eqb_spec a bidder).
          {
            assert (Some a = Some bidder); first easy.
            apply H0 in H2. unfold sumZ_call, call_from_list in H2.
            destruct msg; last easy. destruct m.
            - pose proof (highest_bidder_fact _ _ _ _ _ _ receive_some H1) as [_ ->].
              repeat just_do_it receive_some. inversion receive_some. subst. cbn. inversion Heqo.
              rewrite address_eq_refl. cbn. rewrite H2. now unfold sumZ_act.
            - unfold receive in receive_some. unfold finalize_auction in receive_some.
              destruct (Z.eqb_spec (ctx_amount ctx) 0); last inversion receive_some.
              repeat just_do_it receive_some. inversion receive_some. subst. cbn in *.
              rewrite e1. cbn.
              destruct (address_eqb_spec (auction_seller prev_state) (ctx_from ctx)).
              + cbn. instantiate (CallFacts :=
                                    fun _ ctx prev_state _ _ =>
                                        Some (auction_seller prev_state) <> (auction_highest_bidder prev_state) /\
                                        ctx_from ctx <> ctx_contract_address ctx).
                now unfold CallFacts in facts.
              + now unfold sumZ_act.
          }
          {
            assert (Some a <> Some bidder); first easy.
            apply H0 in H2. unfold sumZ_call, call_from_list in H2. rewrite H2.
            destruct msg; last easy. destruct m.
            - repeat just_do_it receive_some. inversion receive_some. subst.
              cbn. inversion Heqo. rewrite (address_eq_ne _ _ n). now unfold sumZ_act.
            - repeat just_do_it receive_some. inversion receive_some. subst. cbn in *.
              destruct (address_eqb_spec (auction_seller prev_state) (ctx_from ctx)).
              + cbn. now unfold CallFacts in facts.
              + now unfold sumZ_act.
            - unfold receive in receive_some. do 2 just_do_it receive_some.
              + destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state)); try easy.
                just_do_it receive_some.
              + subst. unfold CallFacts in facts. repeat just_do_it receive_some.
                inversion receive_some; subst; cbn in *. easy.
          }
        * assert (None <> Some bidder); first easy.
          unfold receive in receive_some. do 2 just_do_it receive_some.
          {
            destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state)); try just_do_it receive_some.
            repeat just_do_it receive_some. inversion receive_some; subst; cbn in *.
            apply H0 in H2; auto. unfold sumZ_call, call_from_list in H2. rewrite H2.
            now unfold sumZ_act.
          }
          {
            repeat just_do_it receive_some. inversion receive_some; subst; cbn in *; easy.
          }
      + destruct (auction_highest_bidder prev_state) eqn:?.
        * unfold receive in receive_some.
          do 2 just_do_it receive_some.
          {
            destruct (address_eqb_spec (ctx_from ctx) (auction_seller prev_state)); repeat just_do_it receive_some.
            all: inversion receive_some; subst; cbn in *. now inversion H1.
          }
          {
            repeat just_do_it receive_some.
            unfold CallFacts in facts.
            inversion receive_some; subst; cbn in *.
            rewrite H1 in facts. destruct facts. assert (auction_seller prev_state <> bidder); first easy.
            rewrite address_eq_ne; auto. rewrite Heqo in H1.
            apply H0 in H1. unfold sumZ_call, call_from_list in H1. rewrite H1.
            now unfold sumZ_act.
          }
        * unfold receive in receive_some.
          repeat just_do_it receive_some; inversion receive_some; subst; cbn in *; easy.
    - now unfold CallFacts in facts.
    - now unfold CallFacts in facts.
    - now unfold CallFacts in facts.
    - now rewrite <- perm.
    - apply H0 in H1; auto. rewrite H1. unfold sumZ_act. apply (Permutation_filter (fun act : ActionBody => is_act_transfer_to bidder act) _ _) in perm.
      now rewrite <- perm.
    - apply H0 in H1. rewrite H1. unfold sumZ_act. apply (Permutation_filter (fun act : ActionBody => is_act_transfer_to bidder act) _ _) in perm.
      now rewrite <- perm.
    - solve_facts.
      split.
      + pose proof (highest_bidder_not_seller bstate_from to_addr
                      (trace_reachable from_reachable)
                      deployed0).
        now destruct H as (? & ? & ?).
      + pose proof (no_self_calls bstate_from to_addr (trace_reachable from_reachable)
          deployed0) as all.
        destruct all as [? [? [? [? all]]]];
        unfold outgoing_acts in *;
        rewrite queue_prev in *;
        cbn in all;
        destruct_address_eq; cbn in *; auto;
        inversion_clear all as [|? ? hd _];
        destruct msg;
        [contradiction
        | rewrite address_eq_refl in hd;
          congruence].
  Qed.


  (* TODO: correct this theorem *)
  Theorem client_peace_of_mind bstate caddr bidder amount (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate inc_calls,
      incoming_calls Msg trace caddr = Some inc_calls /\
      contract_state bstate caddr = Some cstate /\
      (
        cstate.(auction_highest_bidder) <> Some bidder -> (* exclude the current call *)

        (exists origin tx_body, In (build_tx origin caddr bidder amount tx_body) (outgoing_txs trace caddr)) \/
          In (act_transfer bidder amount)
             (outgoing_acts bstate caddr)
      ).
  Proof with eauto.
  Admitted.

End Theories.
