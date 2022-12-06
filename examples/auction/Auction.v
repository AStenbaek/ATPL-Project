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
   * - #[receive(contract = "auction", name = "bid", payable, mutable, error = "BidError")]
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
    do if (ctx_from ctx =? ctx_contract_address ctx)%address
       then Err default_error
       else Ok tt;
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
        (*do if address_is_contract bidder*)
        do if (ctx_contract_address ctx =? bidder)%address
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

  Ltac just_do_it arg :=
    cbn in *; destruct_match in arg; try congruence.

  Lemma no_self_calls bstate caddr:
    reachable bstate ->
    env_contracts bstate caddr = Some (Auction.contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
        (highest_bidder cstate <> Some caddr /\
         seller cstate <> caddr /\
         Forall (fun abody => match abody with
                           | act_transfer to _ => (to =? caddr)%address = false
                           | _ => False
                           end) (outgoing_acts bstate caddr)).
  Proof with auto.
    contract_induction; intros; (try apply IH in H as H'); cbn in *; auto.
    - split; try split.
      + unfold init in init_some.
        destruct_match in init_some; auto.
        now inversion init_some.
      + unfold init in init_some.
        destruct (address_eqb_spec (ctx_from ctx) (ctx_contract_address ctx));
          [| inversion init_some]; auto.
      + auto.
    - destruct IH as [IH1 [IH2 IH3]]; split; auto.
      inversion IH3; auto.
    - destruct IH as [IH1 [IH2 IH3]]; split;
      try apply Forall_app; try split.
      + unfold receive in receive_some.
        do 2 just_do_it receive_some...
        * do 5 just_do_it receive_some.
          ** inversion receive_some; cbn in *.
             intro.
             inversion H; congruence.
          ** inversion receive_some; cbn in *.
             congruence.
        * do 3 just_do_it receive_some.
          inversion receive_some; cbn in *...
      + unfold receive in receive_some; cbn in *.
        do 2 just_do_it receive_some...
        * do 5 just_do_it receive_some; inversion receive_some...
        * do 3 just_do_it receive_some; inversion receive_some...
      + apply Forall_app; split...
        unfold receive in receive_some.
        do 2 just_do_it receive_some; try (inversion receive_some; auto; fail).
        * do 5 just_do_it receive_some; inversion receive_some...
          apply Forall_cons...
          apply address_eq_ne.
          intro.
          congruence.
        * do 3 just_do_it receive_some; inversion receive_some.
          apply Forall_cons...
          apply address_eq_ne; intro; congruence.
    - destruct IH as [IH1 [IH2 IH3]];
        split; try split.
      + inversion IH3; 
        destruct head; subst...
        destruct action_facts as [A1 [A2 A3]]; subst...
      + inversion IH3; destruct head...
        destruct action_facts as [A1 [A2 A3]]; subst...
      + inversion IH3; apply Forall_app; split...
        unfold receive in receive_some; cbn in *.
        do 2 just_do_it receive_some...
        * do 5 just_do_it receive_some; inversion receive_some...
          apply Forall_cons...
          apply address_eq_ne; intro.
          rewrite H3 in IH1...
        * inversion receive_some...
        * inversion receive_some...
        * do 3 just_do_it receive_some; inversion receive_some...
          apply Forall_cons...
          apply address_eq_ne; intro.
          rewrite H3 in IH2...
    - destruct IH as [IH1 [IH2 IH3]]; repeat split...
      now rewrite <- perm.
    - instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step...
      destruct_action_eval...
  Qed.
