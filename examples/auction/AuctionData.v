(** * Data types for the auction contract *)

From Coq Require Import String.
From Coq Require Import List.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import Utils.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Embedding Require Import Prelude.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import BaseTypes.
Open Scope list.

Import AcornBlockchain Prelude.Maps.
Set Nonrecursive Elimination Schemes.

(** Generating names for the data structures. We also add a prefix, corresponsing ti the current module path. *)
MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp
             ["AuctionState" ; "NotSoldYet"; "Sold";
              "State" ; "mkState"; "auction_state" ; "highest_bidder" ; "item"; "end";
              "InitParameter"; "mkInitParam"; "init_item"; "init_end";
              "BidError"; "OnlyAccount"; "BidTooLow"; "BidTooLate"; "AuctionStillActive"; "AuctionAlreadyFinalized";
              "Msg"; "Bid"; "View"; "ViewHighestBid"; "Finalize";
              (*"Action"; "Transfer";*) "Empty" ] "_coq").

(** ** Definitions of data structures for the contract *)

Definition auction_state_syn :=
  [\ data AuctionState =
       NotSoldYet [_] (* Constructor [list of argument] *)
     | Sold [Address, _] \].

MetaCoq Unquote Inductive (global_to_tc auction_state_syn).

(** The internal state of the contract *)
Definition state_syn : global_dec :=
  [\ record State :=
     mkState {
       auction_state : AuctionState;
       highest_bidder : Maybe Address;
       item : String;
       "end" : Nat
     } \].

Record State_coq : Set := mkState_coq
  {
    auction_state_coq : AuctionState_coq;
    highest_bidder_coq : option nat;
    item_coq : string;
    end_coq : nat;
  }.

Definition params_syn : global_dec :=
  [\
    record InitParameter :=
      mkInitParam {
        init_item : String;
        init_end : Nat
      }
  \].

Record InitParameter_coq : Set :=
  mkInitParam_coq {
    init_item_coq : string;
    init_end_coq : nat
  }.

Definition err_syn : global_dec :=
  [\
    data BidError =
      OnlyAccount [_]
    | BidTooLow [_]
    | BidTooLate [_]
    | AuctionStillActive [_]
    | AuctionAlreadyFinalized [_]
  \].

MetaCoq Unquote Inductive (global_to_tc err_syn).

(* The contract messages *)
Definition msg_syn : global_dec :=
  [\
     data Msg =
       Bid [_]
     | View [_]
     | ViewHighestBid [_]
     | Finalize [_]
  \].

MetaCoq Unquote Inductive (global_to_tc msg_syn).

Module Notations.

  (** Projections *)
  Notation "'auction_state' a" :=
    [| {eConst auction_state} {a} |]
      (in custom expr at level 0).
  Notation "'highest_bidder' a" :=
    [| {eConst highest_bidder} {a} |]
      (in custom expr at level 0).
  Notation "'item' a" :=
    [| {eConst item} {a} |]
      (in custom expr at level 0).
  Notation "'end' a" :=
    [| {eConst (to_string_name <% end_coq %>)} {a} |]
      (in custom expr at level 0).
  Notation "'init_item' a" :=
    [| {eConst init_item} {a} |]
      (in custom expr at level 0).
  Notation "'init_end' a" :=
    [| {eConst init_end} {a} |]
      (in custom expr at level 0).

  Definition actions_ty := [! List SActionBody !].

  Notation "'Result'" := [! Prod State (List SActionBody) !]
                           (in custom type at level 2).

  Definition Σ' :=
    (StdLib.Σ ++ [ Prelude.AcornMaybe;
           auction_state_syn;
           state_syn;
           params_syn;
           err_syn;
           msg_syn;
           AcornBlockchain.SimpleChainAcorn;
           AcornBlockchain.SimpleContractCallContextAcorn;
           AcornBlockchain.SimpleActionBodyAcorn;
           gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                          ("Zneg", [(None,tyInd "positive")])] false
    ])%list.

End Notations.

MetaCoq Run (mkNames "" ["c"; "dl"; "params"] "").

Definition SCtx := to_string_name <% SimpleContractCallContext_coq %>.
Definition SChain := to_string_name <% SimpleChain_coq %>.
