From Coq Require Import Bool.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq Require Import String.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.

Section Auction.
  Context `{Base : ChainBase}.

  Set Nonrecursive Elimination Schemes.
  
  Inductive AuctionState :=
  | not_sold_yet : AuctionState
  | sold : Address -> AuctionState.

  (** 
      /// Type of the parameter to the `init` function
      #[derive(Serialize, SchemaType)]
      struct InitParameter {
      /// The item to be sold
      item:          String,
      /// Time when auction ends using the RFC 3339 format (https://tools.ietf.org/html/rfc3339)
      end:           Timestamp,
      /// The minimum accepted raise to over bid the current bidder in Euro cent.
      minimum_raise: u64,
      }
   *)
  Record Setup :=
    setup {
        setup_seller : Address;
        setup_item : string;
        setup_duration : nat;
        setup_minimum_raise : Amount;
      }.
  
  Record State :=
    build_state {
        auction_state : AuctionState;
        seller : Address;
        item : string;
        duration : nat;
        minimum_raise : Amount;
        current_price : Amount;
        highest_bidder : option Address;
        creation_slot : nat;
      }.

  Definition Error : Type := nat.
  Definition default_error: Error := 1%nat.

  Inductive Msg :=
  | bid
  | view
  | view_highest_bid
  | finalize.

  MetaCoq Run (make_setters State).
  
  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<bid, view, view_highest_bid, finalize>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<setup>.
    
    Global Instance AuctionState_serializable : Serializable AuctionState :=
      Derive Serializable AuctionState_rect<not_sold_yet, sold>.
    
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.
  
  End Serialization.
  
  (** 
   *  Receives:
   *  - #[receive(contract = "auction", name = "bid", payable, mutable, error = "BidError")]
   * - #[receive(contract = "auction", name = "view", return_value = "State")]
   * - #[receive(contract = "auction", name = "viewHighestBid", return_value = "Amount")]
   * - #[receive(contract = "auction", name = "finalize", mutable, error = "FinalizeError")]
   * - 
   *)

  Local Open Scope Z.
  Definition init
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    let seller := ctx_from ctx in
    let item := setup_item setup in
    let duration := setup_duration setup in
    let minimum_raise := setup_minimum_raise setup in
    (* TODO: add checks?*)
    Ok (build_state
          not_sold_yet  (* Item is not sold initially *)
          seller        (* Seller is the creator of the auction *)
          item          (* Item to be sold, represented as a string *)
          duration      (* The number of time slots, auction is running *)
          minimum_raise (* Minimum riase to accept and over bid *)
          0             (* Initial price of item is 0 *)
          None          (* Initial highest bidder *)
          (current_slot chain) (* Slot of contract initialization *)
      ).

  Print act_transfer.
  
  (* TODO: Do we need next_state? *)
  Definition receive
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    (* Placing a bid. *)
    | Some bid =>
        let price := current_price state in
        let min_raise := minimum_raise state in
        let bid_amount := ctx_amount ctx in
        let curr_slot := current_slot chain in
        let start_slot := creation_slot state in
        let dur := duration state in
        let bidder := ctx_from ctx in
        (* Ensure bidder is not a contract *)
        do if address_is_contract bidder
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
          match highest_bidder state with
          | None => []
          | Some addr => [act_transfer addr price]
          end in
        (* Update the state with the new highest bid and bidder *)
        let new_state :=
          state<| current_price := bid_amount |>
               <| highest_bidder := Some bidder |>
        in
        Ok (new_state, action_list)
    | Some view => Ok (state, [])
    | Some view_highest_bid => Ok (state, [])
    | Some finalize =>
        let curr_slot := current_slot chain in
        let start_slot := creation_slot state in
        let dur := duration state in
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
        do bidder <- result_of_option (highest_bidder state) default_error;
        let new_state := state<| auction_state := sold bidder |> in
        Ok (new_state, [act_transfer (seller state) (current_price state)])
    | None => Err default_error
    end.
  
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End Auction.
Section Theories.
  Context `{Base : ChainBase}.
  Open Scope Z.
  Definition bidder ctx new_state :=
    let caddr := ctx_contract_address ctx in
    match highest_bidder new_state with
    | Some addr => (caddr =? addr)%address = false
    | None => False
    end.
  (*
  Lemma try_bidder : forall prev_state new_state chain ctx new_acts,
      (address_is_contract (ctx_contract_address ctx) = true) -> 
      receive chain ctx prev_state (Some bid) = Ok (new_state, new_acts) ->
      bidder ctx new_state.
  Proof.
    intros.
    unfold bidder.
    destruct new_state; cbn.
    destruct highest_bidder0 eqn:Hb.
    - cbn in *.
      remember (address_is_contract (ctx_from ctx)).
      destruct b; try congruence.
      cbn in *
      do 2 (cbn in *; destruct_match in H; try congruence).
      destruct ctx; cbn in *; vm_compute in H; try congruence.
      inversion H.
      rewrite <- H7.
      subst.
      inversion_clear H.
    - do 5 (cbn in *; destruct_match in H; try congruence);
      destruct ctx; cbn in *;
      vm_compute in H;
      try congruence. *)
  
  Lemma no_self_calls bstate caddr:
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    Forall (fun abody => match abody with
                      | act_transfer to _ => (to =? caddr)%address = false
                      | _ => False
                      end) (outgoing_acts bstate caddr).
  Proof.
(*    intros.
    eapply deployed_contract_state_typed in H0 as H'; auto.
    destruct H' as [cstate H'].
    generalize dependent H0.
    generalize dependent H.*)
    contract_induction; intros; cbn in *; auto.
    - now inversion IH.
    - apply Forall_app. split; last apply IH.
      clear IH.
      unfold receive in receive_some.
      destruct_match in receive_some; try inversion receive_some.
      cbn in *; destruct_match in receive_some; try congruence.
      + remember (address_is_contract (ctx_from ctx)).
        destruct b; try congruence.
        do 4 (destruct_match in receive_some; cbn in *; try congruence).
        inversion_clear H0.
        * destruct new_state.
    - apply IH.
    - split.
      + 

      apply Forall_nil.
    - inversion IH.
      apply H2.
    - apply Forall_app.
      split; try apply IH.
      unfold receive in receive_some.
      destruct_match as [[]|] in receive_some.
      + destruct prev_state.
        do 4 (destruct_match in receive_some; cbn in *; try congruence).
        destruct_match in receive_some; cbn in *.
       
        * inversion_clear receive_some.
          constructor; auto.
          eapply address_eq_ne; auto.
          intro; subst.
          
          admit. (* Highest bidder should not be able to be a contract *)
        * now inversion receive_some.
      + inversion receive_some; auto.
      + inversion receive_some; auto.
      + do 3 (destruct_match in receive_some; cbn in *; try congruence).
        inversion_clear receive_some.
        constructor; try constructor.
        admit. (* Similar to previous admit. *)
      + congruence.
    - apply Forall_app; split; [| now inversion IH].
   *) 
                
