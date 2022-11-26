From Coq Require Import Bool.
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From Coq Require Import String.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.

Section Auction.
  Context `{Base : ChainBase}.

  Set Nonrecursive Elimination Schemes.
  
  Inductive AuctionState :=
  | not_sold_yet : AuctionState
  | sold : AuctionState.

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
        highest_bidder : option Address;
        last_action: nat;
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
          None          (* Initial highest bidder *)
          (current_slot chain) (* Slot of contract initialization *)
      ).
          
  
